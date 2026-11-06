"""The text of `.github/workflows/ci.yml`, split into jobs and steps for the workflow tests."""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
"""The repository root."""
GUARD = "env.PLATFORM_RUNS == 'true'"
"""The condition that limits a step to the platforms that check this event."""


def workflow_jobs() -> dict[str, str]:
    """The text of each top-level job, keyed by job id, so tests can scope assertions to one job."""
    text = (ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8")
    body = text[text.index("\njobs:\n") + len("\njobs:\n"):]
    parts = re.split(r"\n(?=  [a-z][a-z0-9-]*:\n)", "\n" + body)
    return {part.strip().split(":", 1)[0]: part for part in parts if part.strip()}


def job_steps(job: str) -> list[str]:
    """The text of each step of one job, in order."""
    return re.split(r"\n      - ", "\n" + job.split("\n    steps:\n", 1)[1])[1:]
