"""The review log may only grow: records are added, never changed or removed.

These tests check `tools/review_log_check.py`, which CI runs in every scope.
"""

import json
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
import unittest

from tests.git_commands import git
from tools.review_log_check import NO_BASE, blob_hash, file_problems, record_problem

REVIEW = json.dumps({"kind": "review", "id": "r1", "commit": "a" * 40, "date": "2026-10-08",
                     "findings": [], "well_formed": True})
RESOLUTION = json.dumps({"kind": "resolution", "finding": "r1-1", "outcome": "fixed", "date": "2026-10-08"})
REVIEW_ID = "20261011T085534Z-6bb34bbf"
REVIEW_FILE = f"reviews/{REVIEW_ID}/review.json"
RESOLUTION_FILE = f"reviews/{REVIEW_ID}/resolution-1-20261011T091200Z.json"
FILE_REVIEW = json.dumps({"kind": "review", "id": REVIEW_ID, "commit": "c" * 40, "date": "2026-10-11",
                          "findings": [{"id": f"{REVIEW_ID}#1"}], "well_formed": True}).encode()
FILE_RESOLUTION = json.dumps({"kind": "resolution", "finding": f"{REVIEW_ID}#1", "outcome": "fixed",
                              "date": "2026-10-11"}).encode()
CHECK_TIMEOUT_SECONDS = 10
"""One check reads two small files from a local repository."""


class RecordTest(unittest.TestCase):
    """Each record file must hold one review or resolution record with its fields."""

    def test_records(self) -> None:
        """Both written kinds pass; text, other JSON values, other kinds and missing fields fail."""
        self.assertIsNone(record_problem(REVIEW))
        self.assertIsNone(record_problem(RESOLUTION))
        broken = {"not json": "not JSON", "[]": "not a JSON object",
                  json.dumps({"kind": "note"}): "unknown record kind 'note'",
                  json.dumps({"kind": 1}): "unknown record kind 1",
                  json.dumps({"kind": "resolution", "finding": "r1-1"}): "missing fields date, outcome"}
        for line, problem in broken.items():
            with self.subTest(line=line):
                self.assertEqual(record_problem(line), problem)


class RecordFileTest(unittest.TestCase):
    """Base record files stay byte-identical; each file holds a valid record at its own path."""

    def test_accepts_new_and_kept_files(self) -> None:
        """New record files pass next to kept base files."""
        base = {REVIEW_FILE: blob_hash(FILE_REVIEW)}
        head = {REVIEW_FILE: FILE_REVIEW, RESOLUTION_FILE: FILE_RESOLUTION}
        self.assertEqual(file_problems(base, head), [])

    def test_refuses_changed_or_removed_files(self) -> None:
        """A changed and a removed base file each name the file."""
        base = {REVIEW_FILE: blob_hash(FILE_REVIEW), RESOLUTION_FILE: blob_hash(FILE_RESOLUTION)}
        head = {REVIEW_FILE: FILE_REVIEW.replace(b"true", b"false")}
        self.assertEqual(file_problems(base, head),
                         [f"{RESOLUTION_FILE}: base record file is changed or removed",
                          f"{REVIEW_FILE}: base record file is changed or removed"])

    def test_refuses_bad_files(self) -> None:
        """Unknown files, invalid records and records at another record's path fail."""
        other = "reviews/20261011T085535Z-6bb34bbf/review.json"
        wrong_finding = RESOLUTION_FILE.replace("resolution-1-", "resolution-2-")
        cases = {"reviews/notes.md": "not a record file", "reviews/notes.jsonl": "not a record file",
                 REVIEW_FILE: "not JSON",
                 other: "review id '20261011T085534Z-6bb34bbf' does not match the path",
                 wrong_finding: f"finding '{REVIEW_ID}#1' does not match the path"}
        contents = {"reviews/notes.md": b"", "reviews/notes.jsonl": FILE_REVIEW + b"\n", REVIEW_FILE: b"{", other: FILE_REVIEW, wrong_finding: FILE_RESOLUTION}
        for path, problem in cases.items():
            with self.subTest(path=path):
                found = file_problems({}, {path: contents[path]})
                self.assertEqual(len(found), 1)
                self.assertTrue(found[0].startswith(f"{path}: ") and problem in found[0], found)
        found = file_problems({}, {REVIEW_FILE: FILE_RESOLUTION})
        self.assertEqual(found, [f"{REVIEW_FILE}: a review.json file must hold a review record"])


class CommandTest(unittest.TestCase):
    """The CI command reads the base log from Git and the head log from the working tree."""

    def run_check(self, root: Path, base: str | None) -> subprocess.CompletedProcess[str]:
        """Run the actual command with an explicit base, as the workflow does."""
        environment = {key: value for key, value in os.environ.items() if key != "REVIEW_LOG_BASE"}
        if base is not None:
            environment["REVIEW_LOG_BASE"] = base
        return subprocess.run([sys.executable, "-m", "tools.review_log_check", "--root", str(root)],
                              cwd=Path(__file__).resolve().parents[1], env=environment,
                              capture_output=True, text=True, timeout=CHECK_TIMEOUT_SECONDS)

    def test_git_base(self) -> None:
        """Added record files pass, a changed base file fails, and a base without reviews or a new
        branch has no base records."""
        with TemporaryDirectory() as directory:
            root = Path(directory)
            git(root, "init", "-q")
            (root / "README.md").write_text("fixture\n")

            def commit() -> str:
                """Record a fixture commit without hooks, signatures or a global identity."""
                git(root, "add", ".")
                git(root, "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                    "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", "commit", "-qm", "fixture")
                return git(root, "rev-parse", "HEAD").decode().strip()

            without_reviews = commit()
            record = root / REVIEW_FILE
            record.parent.mkdir(parents=True)
            record.write_bytes(FILE_REVIEW)
            for base in (without_reviews, NO_BASE, None):
                with self.subTest(base=base):
                    self.assertEqual(self.run_check(root, base).returncode, 0)
            with_file = commit()
            (root / RESOLUTION_FILE).write_bytes(FILE_RESOLUTION)
            self.assertEqual(self.run_check(root, with_file).returncode, 0)
            record.write_bytes(FILE_REVIEW.replace(b"true", b"false"))
            failed = self.run_check(root, with_file)
            self.assertEqual(failed.returncode, 1)
            self.assertIn(f"{REVIEW_FILE}: base record file is changed or removed", failed.stderr)
            self.assertNotEqual(self.run_check(root, "main").returncode, 0)

if __name__ == "__main__":
    unittest.main()
