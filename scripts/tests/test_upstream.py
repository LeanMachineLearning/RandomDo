"""Exercise the checker against real, temporary Git histories; no network access."""

import contextlib
import copy
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import upstream


class UpstreamTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        upstream.git(self.repo, "init", "--quiet")
        upstream.git(self.repo, "config", "user.email", "test@example.invalid")
        upstream.git(self.repo, "config", "user.name", "Upstream tests")
        self.path = self.repo / "src" / "Example.lean"
        self.path.parent.mkdir()
        self.original = (
            "namespace Example\n\n"
            "def foo (x : Nat) : Nat :=\n"
            "  x + 1\n\n"
            "def other : Nat := 10\n\n"
            "end Example\n"
        )
        self.path.write_text(self.original)
        self.before = self.commit()
        self.metadata = {"schema": 1, "commit": self.before, "entries": [{
            "local": "Adapted.foo", "local_file": "RandomDo/Example.lean",
            "upstream": "Example.foo", "path": "src/Example.lean", "start": 3, "end": 4,
        }]}
        self.baseline = upstream.record(None, self.metadata, self.source(), None)

    def source(self):
        return upstream.Source(self.repo)

    def commit(self):
        upstream.git(self.repo, "add", ".")
        upstream.git(self.repo, "commit", "--quiet", "--no-gpg-sign", "-m", "fixture")
        return upstream.git(self.repo, "rev-parse", "HEAD").strip()

    def change(self, text):
        self.path.write_text(text)
        return self.commit()

    def report(self, target):
        return upstream.check(self.baseline, self.source(), target)

    def test_unchanged_and_unrelated_edits(self):
        self.assertEqual(self.report(self.before)["changes"], [])
        target = self.change(self.original.replace("10", "20"))
        self.assertEqual(self.report(target)["changes"], [])

    def test_unrelated_line_insertion_does_not_shift_the_baseline(self):
        target = self.change("-- new module comment\n" + self.original)
        self.assertEqual(self.report(target)["changes"], [])

    def test_statement_and_body_changes(self):
        for old, new in [("x : Nat", "x : Int"), ("x + 1", "x + 2")]:
            with self.subTest(new=new):
                target = self.change(self.original.replace(old, new))
                report = self.report(target)
                self.assertEqual(len(report["changes"]), 1)
                self.assertIn(new, report["changes"][0]["diff"])

    def test_insertions_at_both_boundaries_are_conservatively_reported(self):
        for text in [self.original.replace("def foo", "@[inline]\ndef foo"),
                     self.original.replace("  x + 1\n", "  x + 1\n  + 2\n")]:
            with self.subTest(text=text):
                self.assertEqual(len(self.report(self.change(text))["changes"]), 1)

    def test_replacing_neighboring_lines_can_extend_a_declaration(self):
        for text in [self.original.replace("\n\ndef foo", "\n@[inline]\ndef foo"),
                     self.original.replace("x + 1\n\n", "x + 1\n  + 2\n")]:
            with self.subTest(text=text):
                self.assertTrue(self.report(self.change(text))["changes"])

    def test_deleted_declaration_and_renamed_declaration(self):
        target = self.change(self.original.replace("def foo (x : Nat) : Nat :=\n  x + 1\n", ""))
        self.assertTrue(self.report(target)["changes"])
        target = self.change(self.original.replace("def foo", "def renamed"))
        self.assertTrue(self.report(target)["changes"])

    def test_deleted_or_moved_file_is_reported(self):
        self.path.rename(self.path.with_name("Moved.lean"))
        self.assertTrue(self.report(self.commit())["changes"])

    def test_nonexistent_source_is_an_error(self):
        self.baseline["entries"][0]["path"] = "src/Missing.lean"
        with self.assertRaises(upstream.CheckError):
            self.report(self.before)

    def test_missing_revision_is_an_error(self):
        with self.assertRaises(upstream.CheckError):
            self.report("no-such-revision")

    def test_source_range_and_identity_are_validated(self):
        for key, value in [("start", 0), ("end", 1000), ("path", "../outside.lean")]:
            baseline = copy.deepcopy(self.baseline)
            baseline["entries"][0][key] = value
            with self.subTest(key=key), self.assertRaises(upstream.CheckError):
                upstream.check(baseline, self.source(), self.before)
        baseline = copy.deepcopy(self.baseline)
        baseline["entries"].append(baseline["entries"][0])
        with self.assertRaisesRegex(upstream.CheckError, "Duplicate"):
            upstream.entries(baseline, baseline=True)

    def test_new_removed_and_moved_annotations_require_review(self):
        upstream.validate_mappings(self.baseline, self.metadata)
        for key, value in [("local", "Adapted.new"), ("upstream", "Example.new"),
                           ("local_file", "RandomDo/New.lean")]:
            metadata = copy.deepcopy(self.metadata)
            metadata["entries"][0][key] = value
            with self.subTest(key=key), self.assertRaises(upstream.CheckError):
                upstream.validate_mappings(self.baseline, metadata)

    def test_range_must_match_exported_metadata_at_the_same_commit(self):
        baseline = copy.deepcopy(self.baseline)
        baseline["entries"][0]["start"] = 4
        with self.assertRaisesRegex(upstream.CheckError, "range disagrees"):
            upstream.validate_mappings(baseline, self.metadata)

    def test_invalid_commit_is_a_check_error(self):
        self.baseline["entries"][0]["commit"] = None
        with self.assertRaises(upstream.CheckError):
            upstream.entries(self.baseline, baseline=True)

    def test_partial_review_preserves_other_baselines(self):
        metadata = copy.deepcopy(self.metadata)
        metadata["entries"].append({**metadata["entries"][0], "local": "Adapted.second"})
        baseline = upstream.record(None, metadata, self.source(), None)
        metadata["commit"] = self.change(self.original.replace("x + 1", "x + 2"))
        reviewed = upstream.record(baseline, metadata, self.source(), ["Adapted.foo"])
        by_name = {e["local"]: e for e in reviewed["entries"]}
        self.assertEqual(by_name["Adapted.foo"]["commit"], metadata["commit"])
        self.assertEqual(by_name["Adapted.second"]["commit"], self.before)
        report = upstream.check(reviewed, self.source(), metadata["commit"])
        self.assertEqual([c["local"] for c in report["changes"]], ["Adapted.second"])

    def test_removing_or_renaming_one_annotation_preserves_other_baselines(self):
        for renamed in (False, True):
            with self.subTest(renamed=renamed):
                metadata = copy.deepcopy(self.metadata)
                metadata["entries"].append({**metadata["entries"][0], "local": "Adapted.second"})
                baseline = upstream.record(None, metadata, self.source(), None)
                metadata["commit"] = self.change(self.path.read_text() + "-- unrelated\n")
                metadata["entries"].pop(0)
                selected = ["Adapted.foo"]
                if renamed:
                    metadata["entries"].append({**metadata["entries"][0], "local": "Adapted.new"})
                    selected.append("Adapted.new")
                recorded = upstream.record(baseline, metadata, self.source(), selected)
                upstream.validate_mappings(recorded, metadata)
                by_name = {e["local"]: e for e in recorded["entries"]}
                self.assertNotIn("Adapted.foo", by_name)
                self.assertEqual(by_name["Adapted.second"]["commit"], self.before)
                if renamed:
                    self.assertEqual(by_name["Adapted.new"]["commit"], metadata["commit"])

    def test_git_display_settings_cannot_hide_or_expand_changes(self):
        upstream.git(self.repo, "config", "color.ui", "always")
        upstream.git(self.repo, "config", "diff.interHunkContext", "100")
        (self.repo / ".gitattributes").write_text("*.lean binary\n")
        self.assertFalse(self.report(self.change(self.original.replace("10", "20")))["changes"])
        self.assertTrue(self.report(self.change(self.original.replace("x + 1", "x + 2")))["changes"])

    def test_no_automatic_baseline_update_and_exit_codes(self):
        lock = self.repo / "baseline.json"
        lock.write_text(json.dumps(self.baseline))
        original = lock.read_bytes()
        target = self.change(self.original.replace("x + 1", "x + 2"))
        args = ["--baseline", str(lock), "--repo", str(self.repo), "check", "--target", target]
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(upstream.main(args), 1)
            self.assertEqual(upstream.main(args + ["--advisory"]), 0)
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(upstream.main(args[:-1] + ["missing"] + ["--advisory"]), 2)
        self.assertEqual(lock.read_bytes(), original)

    def test_notification_fingerprint_ignores_unrelated_commits(self):
        changed = self.original.replace("x + 1", "x + 2")
        first = self.report(self.change(changed))
        second = self.report(self.change("-- unrelated\n" + changed))
        self.assertNotEqual(first["target"], second["target"])
        self.assertEqual(first["fingerprint"], second["fingerprint"])

    def test_report_includes_mapping_and_upstream_diff(self):
        report = self.report(self.change(self.original.replace("x + 1", "x + 2")))
        text = upstream.markdown(report)
        for expected in ["Adapted.foo", "Example.foo", "-  x + 1", "+  x + 2"]:
            self.assertIn(expected, text)


if __name__ == "__main__":
    unittest.main()
