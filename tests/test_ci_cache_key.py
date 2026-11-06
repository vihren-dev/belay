"""The check, mutants and publishing jobs calculate one cache key for the Nix store of a commit (#326)."""

from pathlib import Path
import os
import re
import subprocess

import pytest

from tests.ci_workflow_text import ROOT, job_steps, workflow_jobs

pytestmark = [pytest.mark.unit]


def tree_hash_command(job: str) -> str:
    """The shell command of the step that hashes the tracked files for the cache key."""
    step = next(step for step in job_steps(job) if "id: tree" in step)
    return re.search(r"\n        run: (.+)", step).group(1)


def test_every_job_keys_the_store_by_the_tracked_files_before_writing_into_the_checkout() -> None:
    """The check, mutants and publishing jobs use one cache key, whose tree part comes from the
    same command, run directly after the checkout, before any step can write files into it (#326)."""
    jobs = workflow_jobs()
    assert len({tree_hash_command(job) for job in jobs.values()}) == 1
    for name, job in jobs.items():
        assert "${{ steps.tree.outputs.hash }}" in re.search(r"primary-key: (.+)", job).group(1), name
        steps = job_steps(job)
        tree = next(index for index, step in enumerate(steps) if "id: tree" in step)
        assert steps[tree - 1].startswith("uses: actions/checkout@"), name
        assert all("Skip macOS checks" in step for step in steps[:tree - 1]), name
    assert "hashFiles('**'" not in (ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8")


def test_tree_hash_ignores_untracked_files_and_task_records(tmp_path: Path) -> None:
    """The tree hash of the cache key changes with a tracked file outside plans/ and reviews/
    only: Python caches and build outputs that a job writes, and task records, keep it (#326)."""
    command = tree_hash_command(workflow_jobs()["check"])

    def tree_hash() -> str:
        """Run the workflow's command in the temporary repository and read its step output."""
        output = tmp_path / "output"
        output.write_text("")
        subprocess.run(["bash", "-c", command], cwd=tmp_path / "repository", check=True, timeout=10,
                       env={**os.environ, "GITHUB_OUTPUT": str(output)})
        return output.read_text()

    repository = tmp_path / "repository"
    for name in ("tools/check.py", "plans/task.md", "reviews/record.json"):
        (repository / name).parent.mkdir(parents=True, exist_ok=True)
        (repository / name).write_text(name)
    for arguments in (["init", "-q"], ["add", "."]):
        subprocess.run(["git", *arguments], cwd=repository, check=True, timeout=10)
    first = tree_hash()
    assert re.fullmatch(r"hash=[0-9a-f]{40}\n", first), first
    (repository / "tools/__pycache__").mkdir()
    (repository / "tools/__pycache__/check.cpython-312.pyc").write_bytes(b"compiled")
    (repository / "build").mkdir()
    (repository / "build/result").write_text("output")
    (repository / "plans/task.md").write_text("changed task record")
    (repository / "reviews/record.json").write_text("changed review record")
    subprocess.run(["git", "add", "plans", "reviews"], cwd=repository, check=True, timeout=10)
    assert tree_hash() == first
    (repository / "tools/check.py").write_text("changed code")
    subprocess.run(["git", "add", "tools/check.py"], cwd=repository, check=True, timeout=10)
    assert tree_hash() != first
