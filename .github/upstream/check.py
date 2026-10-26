#!/usr/bin/env python3
"""Track changes to annotated Lean core declarations. Python standard library only."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from functools import cache
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[2]
REPOSITORY = "https://github.com/leanprover/lean4"
BASELINE = Path(__file__).with_name("baseline.json")
SHA = re.compile(r"[0-9a-f]{40}\Z")
HUNK = re.compile(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


class CheckError(Exception):
    """An incomplete check must fail, rather than report that nothing changed."""


def git(repo: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "--no-pager", "-C", str(repo), *args],
        encoding="utf-8", stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if result.returncode:
        raise CheckError(f"git {' '.join(args)} failed: {result.stderr.strip()}")
    return result.stdout


def validate_ref(ref: str) -> None:
    if not re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_./-]*", ref) or ".." in ref:
        raise CheckError(f"Invalid upstream revision: {ref!r}")


class Source:
    def __init__(self, repo: Path | None):
        self.fetch = repo is None
        self.repo = repo or ROOT / ".lake" / "upstream-lean.git"
        if self.fetch and not self.repo.exists():
            self.repo.mkdir(parents=True)
            git(self.repo, "init", "--bare")
        self.revisions: dict[str, str] = {}

    def resolve(self, ref: str) -> str:
        validate_ref(ref)
        if ref not in self.revisions:
            if self.fetch:
                # Fetch only data from the fixed upstream repository; never check out or execute it.
                git(self.repo, "fetch", "--quiet", "--depth=1", "--no-tags",
                    REPOSITORY + ".git", ref)
                commit = git(self.repo, "rev-parse", "FETCH_HEAD^{commit}").strip()
            else:
                commit = git(self.repo, "rev-parse", "--verify", ref + "^{commit}").strip()
            if not SHA.fullmatch(commit):
                raise CheckError(f"Not an upstream commit: {commit!r}")
            self.revisions[ref] = commit
            self.revisions[commit] = commit
        return self.revisions[ref]

    @cache
    def read(self, commit: str, path: str) -> str:
        return git(self.repo, "show", f"{commit}:{path}")

    @cache
    def diff(self, before: str, after: str, path: str) -> str:
        # Zero context makes each hunk one contiguous edit. Ignore local display settings and
        # attributes that could otherwise color the patch, merge hunks, or hide text as binary.
        return git(self.repo, "diff", "--no-color", "--text", "--no-ext-diff", "--no-textconv",
                   "--no-renames", "--unified=0", "--inter-hunk-context=0",
                   "--diff-algorithm=myers", "--no-indent-heuristic", before, after, "--", path)


def read_json(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict) or value.get("schema") != 1:
        raise CheckError(f"Unsupported metadata schema in {path}")
    return value


def identity(entry: dict) -> tuple[str, str]:
    return entry["local"], entry["upstream"]


def entries(document: dict, *, baseline: bool) -> dict[tuple[str, str], dict]:
    records = document.get("entries")
    if not isinstance(records, list) or not records:
        raise CheckError("Expected a nonempty list of tracked declarations")
    result = {}
    for entry in records:
        if not isinstance(entry, dict):
            raise CheckError("Invalid tracked declaration")
        for field in ("local", "upstream", "path", "local_file"):
            if not isinstance(entry.get(field), str) or not entry[field].strip():
                raise CheckError(f"Missing {field} in tracked declaration")
        for field in ("path", "local_file"):
            path = PurePosixPath(entry[field])
            if path.is_absolute() or ".." in path.parts or not entry[field].endswith(".lean"):
                raise CheckError(f"Invalid source path: {entry[field]}")
        if not entry["path"].startswith("src/"):
            raise CheckError(f"Not a Lean core source path: {entry['path']}")
        start, end = entry.get("start"), entry.get("end")
        if type(start) is not int or type(end) is not int or not 1 <= start <= end:
            raise CheckError(f"Invalid source range for {entry['upstream']}")
        if baseline and (not isinstance(entry.get("commit"), str) or not SHA.fullmatch(entry["commit"])):
            raise CheckError(f"Invalid baseline commit for {entry['upstream']}")
        key = identity(entry)
        if key in result:
            raise CheckError(f"Duplicate upstream mapping: {key}")
        result[key] = entry
    if baseline and document.get("repository") != REPOSITORY:
        raise CheckError("The baseline must refer to leanprover/lean4")
    if not baseline and (not isinstance(document.get("commit"), str)
                         or not SHA.fullmatch(document["commit"])):
        raise CheckError("The exporter must run with a Lean toolchain carrying a full commit hash")
    return result


def validate_mappings(baseline: dict, metadata: dict) -> None:
    old, current = entries(baseline, baseline=True), entries(metadata, baseline=False)
    missing, removed = current.keys() - old.keys(), old.keys() - current.keys()
    if missing or removed:
        raise CheckError(
            f"Annotations and baseline disagree. New mappings: {sorted(missing)}; "
            f"removed mappings: {sorted(removed)}. Review and record the affected declarations."
        )
    for key in old:
        if old[key]["local_file"] != current[key]["local_file"]:
            raise CheckError(f"{key[0]} moved locally; record its new location after review")
        if old[key]["commit"] == metadata["commit"]:
            if any(old[key][field] != current[key][field] for field in ("path", "start", "end")):
                raise CheckError(f"Baseline range disagrees with Lean's metadata for {key[1]}")


def validate_range(source: Source, commit: str, entry: dict) -> None:
    if entry["end"] > len(source.read(commit, entry["path"]).splitlines()):
        raise CheckError(f"Source range exceeds {entry['path']} at {commit}")


def changed_hunks(diff: str, start: int, end: int) -> list[str]:
    """Select zero-context hunks touching the inclusive baseline range."""
    result = []
    for hunk in re.split(r"(?m)^(?=@@ -)", diff)[1:]:
        match = HUNK.match(hunk)
        if match is None:
            raise CheckError("Invalid Git diff hunk")
        first = int(match[1])
        count = int(match[2]) if match[2] is not None else 1
        # A pure insertion is anchored after `first`. Include both boundaries because a new
        # attribute or trailing clause can extend the declaration beyond its old source range.
        if count == 0:
            touches = start - 1 <= first <= end
        else:
            # Replacing a neighboring line can also add an attribute or trailing clause.
            added = int(match[4]) if match[4] is not None else 1
            margin = 1 if added else 0
            touches = first <= end + margin and first + count > start - margin
        if touches:
            result.append(hunk.rstrip("\n"))
    return result


def check(baseline: dict, source: Source, target: str) -> dict:
    tracked = entries(baseline, baseline=True)
    target = source.resolve(target)
    changes = []
    for key in sorted(tracked):
        entry = tracked[key]
        before = source.resolve(entry["commit"])
        validate_range(source, before, entry)
        hunks = changed_hunks(source.diff(before, target, entry["path"]), entry["start"], entry["end"])
        if hunks:
            changes.append({**entry, "diff": "\n".join(hunks)})
    # Exclude hunk headings: unrelated insertions can shift the target's line numbers.
    edits = [{**c, "diff": "\n".join(line for line in c["diff"].splitlines()
                                  if not line.startswith("@@ "))} for c in changes]
    fingerprint = hashlib.sha256(json.dumps(edits, sort_keys=True).encode()).hexdigest()
    return {"target": target, "checked": len(tracked), "changes": changes,
            "fingerprint": fingerprint}


def record(baseline: dict | None, metadata: dict, source: Source,
           selected: list[str] | None) -> dict:
    current = entries(metadata, baseline=False)
    old = entries(baseline, baseline=True) if baseline is not None else {}
    names = {key[0] for key in old.keys() | current.keys()}
    chosen = set(selected) if selected else names
    if not chosen <= names:
        raise CheckError(f"Unknown tracked declarations: {sorted(chosen - names)}")
    # Include old names so --only can remove or rename an annotation without advancing others.
    result = {key: value for key, value in old.items() if selected and key[0] not in chosen}
    commit = source.resolve(metadata["commit"])
    for key, entry in current.items():
        if key[0] in chosen:
            validate_range(source, commit, entry)
            result[key] = {**entry, "commit": commit}
    return {"schema": 1, "repository": REPOSITORY,
            "entries": [result[key] for key in sorted(result)]}


def markdown(report: dict) -> str:
    lines = ["# Lean core changes affecting adapted definitions", "",
             f"Checked {report['checked']} mappings against "
             f"[{report['target'][:12]}]({REPOSITORY}/commit/{report['target']}).", ""]
    if not report["changes"]:
        lines.append("No changes intersect the tracked declarations since their recorded baselines.")
    else:
        lines += ["Review these changes before advancing the affected baselines.", ""]
        for change in report["changes"]:
            link = (f"{REPOSITORY}/blob/{change['commit']}/{change['path']}"
                    f"#L{change['start']}-L{change['end']}")
            lines += [f"## `{change['local']}`", "",
                      f"Local file: `{change['local_file']}`. "
                      f"Upstream: [`{change['upstream']}`]({link}).", "",
                      "````diff",
                      change["diff"], "````", ""]
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, default=BASELINE)
    parser.add_argument("--repo", type=Path, help="Use an existing Lean Git repository without fetching")
    commands = parser.add_subparsers(dest="command", required=True)
    check_parser = commands.add_parser("check", help="Report upstream changes; never update the baseline")
    check_parser.add_argument("--metadata", type=Path, help="Exported annotations from the current build")
    check_parser.add_argument("--target", help="Upstream revision (defaults to the exported Lean commit)")
    check_parser.add_argument("--report", type=Path)
    check_parser.add_argument("--json-report", type=Path)
    check_parser.add_argument("--advisory", action="store_true",
                              help="Exit successfully on drift, but not on errors")
    record_parser = commands.add_parser("record", help="Record explicitly reviewed upstream baselines")
    record_parser.add_argument("--metadata", type=Path, required=True)
    choice = record_parser.add_mutually_exclusive_group(required=True)
    choice.add_argument("--only", nargs="+", metavar="DECL")
    choice.add_argument("--all", action="store_true")
    args = parser.parse_args(argv)
    try:
        baseline = read_json(args.baseline) if args.baseline.exists() else None
        metadata = read_json(args.metadata) if args.metadata else None
        source = Source(args.repo)
        if args.command == "record":
            result = record(baseline, metadata, source, args.only)
            args.baseline.write_text(
                json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
            print(f"Recorded {len(result['entries'])} mappings in {args.baseline}")
            return 0
        if baseline is None:
            raise CheckError("No baseline; review the mappings and run the record command first")
        if metadata:
            validate_mappings(baseline, metadata)
        target = args.target or (metadata["commit"] if metadata else None)
        if target is None:
            raise CheckError("check requires --metadata or --target")
        report = check(baseline, source, target)
        text = markdown(report)
        if args.report:
            args.report.write_text(text, encoding="utf-8")
        else:
            print(text, end="")
        if args.json_report:
            args.json_report.write_text(
                json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        return 1 if report["changes"] and not args.advisory else 0
    except (CheckError, OSError, ValueError) as exc:
        print(f"Upstream check failed: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
