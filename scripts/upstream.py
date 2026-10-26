#!/usr/bin/env python3
"""Track changes to annotated Lean core declarations. Python standard library only."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "https://github.com/leanprover/lean4"
LOCK = ROOT / "upstream.json"
SHA = re.compile(r"[0-9a-f]{40}\Z")
HUNK = re.compile(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


class CheckError(Exception):
    """An incomplete check must fail, rather than report that nothing changed."""


def git(repo: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "--no-pager", "-C", str(repo), *args],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if result.returncode:
        raise CheckError(f"git {' '.join(args)} failed: {result.stderr.strip()}")
    return result.stdout


def valid_ref(ref: str) -> str:
    if not re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_./-]*", ref) or ".." in ref:
        raise CheckError(f"Invalid upstream revision: {ref!r}")
    return ref


class Source:
    def __init__(self, repo: Path | None):
        self.fetch = repo is None
        self.repo = repo or ROOT / ".lake" / "upstream-lean.git"
        if self.fetch and not self.repo.exists():
            self.repo.mkdir(parents=True)
            git(self.repo, "init", "--bare")
        self.revisions: dict[str, str] = {}
        self.files: dict[tuple[str, str], str] = {}
        self.diffs: dict[tuple[str, str, str], str] = {}

    def resolve(self, ref: str) -> str:
        valid_ref(ref)
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

    def read(self, commit: str, path: str) -> str:
        key = (commit, path)
        if key not in self.files:
            self.files[key] = git(self.repo, "show", f"{commit}:{path}")
        return self.files[key]

    def diff(self, before: str, after: str, path: str) -> str:
        key = (before, after, path)
        if key not in self.diffs:
            self.diffs[key] = git(
                self.repo, "diff", "--no-ext-diff", "--no-textconv", "--no-renames",
                "--unified=3", before, after, "--", path,
            )
        return self.diffs[key]


def read_json(path: Path) -> dict:
    value = json.loads(path.read_text())
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
        if baseline:
            if not isinstance(entry.get("commit"), str) or not SHA.fullmatch(entry["commit"]):
                raise CheckError(f"Invalid baseline commit for {entry['upstream']}")
            if not isinstance(entry.get("sha256"), str) or not re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]):
                raise CheckError(f"Missing source hash for {entry['upstream']}")
            if not isinstance(entry.get("note"), str) or not entry["note"].strip():
                raise CheckError(f"Missing review note for {entry['local']}")
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


def source_hash(source: Source, commit: str, entry: dict) -> str:
    lines = source.read(commit, entry["path"]).splitlines(keepends=True)
    if entry["end"] > len(lines):
        raise CheckError(f"Source range exceeds {entry['path']} at {commit}")
    text = "".join(lines[entry["start"] - 1:entry["end"]])
    return hashlib.sha256(text.encode()).hexdigest()


@dataclass
class Hunk:
    old_start: int
    lines: list[str]

    def edits(self, start: int, end: int) -> list[list[str]]:
        """Return relevant edit blocks, excluding context and unrelated edits in the same hunk."""
        line = self.old_start
        result, block, affected = [], [], False
        for text in self.lines[1:]:
            if text.startswith("+"):
                # Include insertions at either boundary: these can extend a declaration.
                affected |= start - 1 <= line - 1 <= end
                block.append(text)
            elif text.startswith("-"):
                affected |= start <= line <= end
                block.append(text)
                line += 1
            elif text.startswith(" "):
                if affected:
                    result.append(block)
                block, affected = [], False
                line += 1
        if affected:
            result.append(block)
        return result


def hunks(diff: str) -> list[Hunk]:
    result: list[Hunk] = []
    for line in diff.splitlines():
        match = HUNK.match(line)
        if match:
            result.append(Hunk(int(match[1]), [line]))
        elif result:
            result[-1].lines.append(line)
    return result


def check(baseline: dict, source: Source, target: str) -> dict:
    tracked = entries(baseline, baseline=True)
    target = source.resolve(target)
    changes = []
    for key in sorted(tracked):
        entry = tracked[key]
        before = source.resolve(entry["commit"])
        if source_hash(source, before, entry) != entry["sha256"]:
            raise CheckError(f"Baseline source hash mismatch for {entry['upstream']}")
        relevant = [(h, h.edits(entry["start"], entry["end"]))
                    for h in hunks(source.diff(before, target, entry["path"]))]
        relevant = [(h, edits) for h, edits in relevant if edits]
        if relevant:
            changes.append({**entry, "diff": "\n".join(
                line for h, _ in relevant for line in h.lines),
                "edits": [block for _, edits in relevant for block in edits]})
    # Unrelated upstream commits must not cause repeated issue updates. Hunk offsets may change
    # when unrelated lines are inserted earlier in the file, so exclude them from the digest.
    fingerprint = hashlib.sha256(json.dumps([
        [c["local"], c["local_file"], c["upstream"], c["path"], c["commit"],
         c["start"], c["end"], c["note"], c["edits"]]
        for c in changes
    ], ensure_ascii=False, sort_keys=True).encode()).hexdigest()
    return {"target": target, "checked": len(tracked), "changes": changes,
            "fingerprint": fingerprint}


def record(baseline: dict | None, metadata: dict, source: Source,
           selected: list[str] | None, note: str) -> dict:
    current = entries(metadata, baseline=False)
    old = entries(baseline, baseline=True) if baseline is not None else {}
    if not note.strip():
        raise CheckError("A review note is required")
    names = {key[0] for key in current}
    chosen = set(selected) if selected else names
    if not chosen <= names:
        raise CheckError(f"Unknown tracked declarations: {sorted(chosen - names)}")
    # --all also removes annotations that were deleted; --only preserves all other baselines.
    result = {key: value for key, value in old.items() if selected and key[0] not in chosen}
    commit = source.resolve(metadata["commit"])
    for key, entry in current.items():
        if key[0] in chosen:
            result[key] = {**entry, "commit": commit,
                           "sha256": source_hash(source, commit, entry), "note": note}
    return {"schema": 1, "repository": REPOSITORY,
            "entries": [result[key] for key in sorted(result)]}


def markdown(report: dict) -> str:
    lines = ["# Lean core changes affecting adapted definitions", "",
             f"Checked {report['checked']} mappings against "
             f"[{report['target'][:12]}]({REPOSITORY}/commit/{report['target']}).", ""]
    if not report["changes"]:
        lines.append("No changes intersect the tracked declarations since their recorded baselines.")
    else:
        lines += ["Review these upstream changes, then port them or explain why they do not apply. "
                  "Advance a declaration's baseline only after that review. "
                  "A moved or deleted source file is reported as a deletion.", ""]
        for change in report["changes"]:
            link = (f"{REPOSITORY}/blob/{change['commit']}/{change['path']}"
                    f"#L{change['start']}-L{change['end']}")
            lines += [f"## `{change['local']}`", "",
                      f"Local file: `{change['local_file']}`. "
                      f"Upstream: [`{change['upstream']}`]({link}).", "",
                      f"Baseline note: {change['note']}", "",
                      f"[Full upstream comparison]({REPOSITORY}/compare/"
                      f"{change['commit']}...{report['target']})", "", "````diff",
                      change["diff"], "````", ""]
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, default=LOCK)
    parser.add_argument("--repo", type=Path, help="Use an existing Lean Git repository without fetching")
    commands = parser.add_subparsers(dest="command", required=True)
    check_parser = commands.add_parser("check", help="Report upstream changes; never update the baseline")
    check_parser.add_argument("--metadata", type=Path, help="Exported annotations from the current build")
    check_parser.add_argument("--target", help="Upstream revision (defaults to the exported Lean commit)")
    check_parser.add_argument("--report", type=Path)
    check_parser.add_argument("--json-report", type=Path)
    check_parser.add_argument("--advisory", action="store_true", help="Exit successfully on drift, but not on errors")
    record_parser = commands.add_parser("record", help="Record explicitly reviewed upstream baselines")
    record_parser.add_argument("--metadata", type=Path, required=True)
    choice = record_parser.add_mutually_exclusive_group(required=True)
    choice.add_argument("--only", nargs="+", metavar="DECL")
    choice.add_argument("--all", action="store_true")
    record_parser.add_argument("--note", required=True)
    args = parser.parse_args(argv)
    try:
        baseline = read_json(args.baseline) if args.baseline.exists() else None
        metadata = read_json(args.metadata) if args.metadata else None
        source = Source(args.repo)
        if args.command == "record":
            result = record(baseline, metadata, source, args.only, args.note)
            args.baseline.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
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
            args.report.write_text(text)
        else:
            print(text, end="")
        if args.json_report:
            args.json_report.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
        return 1 if report["changes"] and not args.advisory else 0
    except (CheckError, OSError, ValueError) as exc:
        print(f"Upstream check failed: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
