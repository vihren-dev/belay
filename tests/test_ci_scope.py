"""Prevent CI routing from skipping model, parser or build changes or weakening the full checks."""

from pathlib import Path
from tempfile import TemporaryDirectory
import json
import os
import subprocess
import sys
import unittest

from tests.git_commands import git
from tests.ci_scope import scope


class CiScopeTest(unittest.TestCase):
    """Keep the documentation, test, infrastructure and full scopes explicit and conservative."""

    def test_change_scopes(self) -> None:
        """Unknown paths run the Nix targets; host checks run only for their own subjects."""
        examples = [(["README.md", "docs/ci.md"], "docs"), (["plans/20261007-task.md"], "docs"),
                    (["docs/nested/guide.md"], "docs"), (["unknown/file.md"], "test"),
                    (["reviews/other.jsonl"], "test"), (["reviews/notes.md"], "test"),
                    (["reviews/20261011T085534Z-6bb34bbf/review.json"], "docs"),
                    (["reviews/20261011T085534Z-6bb34bbf/resolution-2-20261011T091200Z.json",
                      "docs/ci.md"], "docs"),
                    (["reviews/20261011T085534Z-6bb34bbf/review.json", "tools/review.py"], "test"),
                    (["reviews/20261011T085534Z-6bb34bbf/review.json", "parser/library.c"], "full"),
                    (["reviews/20261011T085534Z-6bb34bbf/notes.json"], "test"),
                    (["reviews/review.json"], "test"),
                    (["parser/upstream/README.md"], "full"),
                    (["packages/belay-sqlite-model/Belay/Sqlite/Model/PreservationLaws.lean"], "test"),
                    (["tests/coverage_test.py"], "test"), (["unknown/file"], "test"),
                    (["tools/review.py"], "test"), (["belay/sqlite/sql_model.py"], "test"),
                    (["nix/flake.lock"], "full"),
                    (["tools/check_resources.py"], "infrastructure"),
                    (["build-support/default.nix"], "full"),
                    (["build-support/tests.nix"], "infrastructure"),
                    (["tests/test_toolchain_smoke.py"], "test"),
                    (["tests/test_source_identity.py"], "infrastructure"),
                    (["tests/test_nix_test_targets.py"], "infrastructure"),
                    (["tests/environment_snapshot_test.py"], "infrastructure"),
                    (["tests/nix_suites.json"], "infrastructure"),
                    (["pytest.ini"], "infrastructure"), (["tests/conftest.py"], "infrastructure"),
                    (["conftest.py"], "infrastructure"),
                    (["tests/runtime_support.py"], "infrastructure"),
                    (["tests/new_shared_helper.py"], "infrastructure"),
                    (["tests/test_translation.py"], "test"),
                    (["README.md", "parser/library.c"], "full"),
                    ([".github/workflows/ci.yml"], "full"), ([], "full")]
        for paths, expected in examples:
            with self.subTest(paths=paths):
                self.assertEqual(scope(paths, "pull_request"), expected)

    def test_full_runs(self) -> None:
        """Manual, scheduled and main runs check everything; main skips only docs."""
        self.assertEqual(scope(["README.md"], "workflow_dispatch"), "full")
        self.assertEqual(scope([], "schedule"), "full")
        self.assertEqual(scope(["tests/test_translation.py"], "push"), "full")
        self.assertEqual(scope(["docs/ci.md"], "push"), "docs")

    def test_real_diff_preserves_removed_runtime_paths(self) -> None:
        """Renaming parser source to Markdown still runs every check, using the actual CI entrypoint."""
        with TemporaryDirectory() as directory:
            root = Path(directory)
            git(root, "init", "-q")
            (root / "parser").mkdir()
            source = root / "parser/library.c"
            source.write_text("fixture")

            def commit() -> str:
                """Record a local fixture without hooks, signatures or global identity requirements."""
                git(root, "add", ".")
                git(root, "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                    "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", "commit", "-qm", "fixture")
                return git(root, "rev-parse", "HEAD").decode().strip()

            base = commit()
            (root / "docs").mkdir()
            source.rename(root / "docs/main.md")
            commit()
            event, output = root / "event.json", root / "output"
            event.write_text(json.dumps({"pull_request": {"base": {"sha": base}}}))
            environment = {**os.environ, "GITHUB_EVENT_NAME": "pull_request",
                           "GITHUB_EVENT_PATH": str(event), "GITHUB_OUTPUT": str(output),
                           "PYTHONPATH": str(Path(__file__).resolve().parents[1])}
            subprocess.run([sys.executable, "-m", "tests.ci_scope"], cwd=root,
                           env=environment, check=True, capture_output=True, timeout=10)
            self.assertEqual(output.read_text(), "scope=full\n")


if __name__ == "__main__":
    unittest.main()
