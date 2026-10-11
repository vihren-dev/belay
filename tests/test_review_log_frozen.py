"""`just review-log-frozen` (`tools/review_log_frozen.py`) tells when the frozen review log can
be converted: when no unmerged branch or workspace has a line that `main` lacks."""

import os
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

from tools.review_log_frozen import Head, describe, missing_lines

ROOT = Path(__file__).resolve().parents[1]
JJ_TIMEOUT_SECONDS = 10
"""One jj command in a fixture repository with a few small files."""
MAIN = frozenset({"a", "b"})


@pytest.mark.unit
@pytest.mark.parametrize("lines,missing,state", [
    ({"a", "b"}, 0, "same as main"),
    ({"a"}, 0, "older than main"),
    (set(), 0, "older than main"),
    ({"a", "c"}, 1, "1 line that main lacks"),
    ({"c", "d"}, 2, "2 lines that main lacks"),
])
def test_compare_with_main(lines: set[str], missing: int, state: str) -> None:
    """`missing_lines` and `describe`: only lines that main lacks block the conversion; an older
    log does not."""
    head = Head("0" * 40, "feature", frozenset(lines))
    assert missing_lines(MAIN, head) == missing
    assert describe(MAIN, head) == f"000000000000 feature: {state}"


def jj(repository: Path, *arguments: str) -> None:
    """Run one jj command in the fixture with a fixed identity and no user configuration."""
    environment = {**os.environ, "JJ_CONFIG": str(repository.parent / "config.toml"),
                   "JJ_USER": "Test", "JJ_EMAIL": "test@example.invalid"}
    subprocess.run(["jj", *arguments], cwd=repository, env=environment, check=True, capture_output=True,
                   timeout=JJ_TIMEOUT_SECONDS)


@pytest.mark.integration
@pytest.mark.skipif(shutil.which("jj") is None, reason="jj is not installed")
def test_command_on_a_jj_repository(tmp_path: Path) -> None:
    """`tools.review_log_frozen.main` on a real jj repository: a merged bookmark with an older log
    is ignored; an unmerged bookmark with a new line blocks until main has the line."""
    (tmp_path / "config.toml").write_text("")
    repository = tmp_path / "repository"
    repository.mkdir()
    log = repository / "reviews" / "log.jsonl"
    log.parent.mkdir()
    jj(repository, "git", "init")
    log.write_text("a\n")
    jj(repository, "commit", "-m", "old")
    jj(repository, "bookmark", "create", "old", "-r", "@-")
    log.write_text("a\nb\n")
    jj(repository, "commit", "-m", "main")
    jj(repository, "bookmark", "create", "main", "-r", "@-")
    log.write_text("a\nb\nc\n")
    jj(repository, "commit", "-m", "feature")
    jj(repository, "bookmark", "create", "feature", "-r", "@-")

    def report() -> subprocess.CompletedProcess[str]:
        """Run the real command on the fixture repository."""
        return subprocess.run([sys.executable, "-m", "tools.review_log_frozen", "--root", str(repository)],
                              cwd=ROOT, capture_output=True, text=True, timeout=JJ_TIMEOUT_SECONDS * 3)

    blocked = report()
    assert blocked.returncode == 1, blocked.stderr
    assert "feature: 1 line that main lacks" in blocked.stdout and " old:" not in blocked.stdout
    jj(repository, "bookmark", "set", "main", "-r", "feature")
    converted = report()
    assert converted.returncode == 0, converted.stderr
    assert "The frozen log can be converted." in converted.stdout
