"""The `mutants` job of `.github/workflows/ci.yml` runs each mutant suite on its own runner and
reuses the report of an accepted run of the same Nix derivation (#328)."""

import json
import re

import pytest

from tests.ci_workflow_text import GUARD, ROOT, job_steps, workflow_jobs

pytestmark = [pytest.mark.unit]

ELIGIBLE = "(github.event_name == 'schedule' || (github.event_name == 'push' && github.ref == 'refs/heads/main'))"
"""The events whose passed runs may save a result for later runs."""
REUSED = "steps.accepted.outputs.cache-hit != 'true'"
"""The condition of the steps that a reused report replaces."""


def named_step(job: str, name: str) -> str:
    """The text of the step of `job` with this name."""
    return next(step for step in job_steps(job) if step.startswith(f"name: {name}\n"))


def test_mutant_job_runs_each_mutant_suite_for_the_full_scope() -> None:
    """The mutants job runs each suite of tests/nix_mutant_suites.json on its own runner, only
    for the full scope and with the platform guard of the check job, and never saves a Nix store."""
    job = workflow_jobs()["mutants"]
    suites = json.loads((ROOT / "tests/nix_mutant_suites.json").read_text())
    assert f"suite: [{', '.join(suites)}]" in job
    assert "save: false" in job and "save: ${{" not in job
    assert "timeout-minutes: 75" in job
    steps = job_steps(job)
    working = [step for step in steps if "Skip macOS checks" not in step]
    assert all(GUARD in step for step in working)
    full = "steps.scope.outputs.scope == 'full'"
    assert all(full in step for step in working
               if "checkout" not in step and "id: scope" not in step and "id: tree" not in step)
    assert 'just test-mutants "$MUTANT_SUITE"' in job


def test_a_report_is_reused_only_for_the_same_derivation_and_platform() -> None:
    """The restore and the save use one key: the platform and the derivation of the suite that
    `just test-mutants` builds, so any change of an input of the suite runs it again."""
    job = workflow_jobs()["mutants"]
    suite = named_step(job, "Find the Nix derivation of the mutant suite")
    assert 'nix-instantiate build-support/default.nix -A "scheduledTests.$MUTANT_SUITE"' in suite
    justfile = (ROOT / "justfile").read_text(encoding="utf-8")
    assert 'nix-build build-support/default.nix -A "scheduledTests.{{suite}}"' in justfile
    key = "key: mutant-report-v1-${{ matrix.system }}-${{ steps.suite.outputs.derivation }}"
    restore = named_step(job, "Restore the report of an accepted run of this derivation")
    save = named_step(job, "Save the report of this accepted derivation")
    assert key in restore and key in save
    assert re.search(r"uses: actions/cache/restore@[0-9a-f]{40} ", restore)
    assert re.search(r"uses: actions/cache/save@[0-9a-f]{40} ", save)
    assert "path: build/mutant-accepted/" in restore and "path: build/mutant-accepted/" in save


def test_a_reused_report_replaces_the_run_and_only_a_passed_eligible_run_saves() -> None:
    """A restored report skips the store restore and the run; the job retains the reused report.
    Only a passed main push or nightly run saves a report, and only one that it ran itself."""
    job = workflow_jobs()["mutants"]
    assert REUSED in named_step(job, "Restore Nix builds")
    run = named_step(job, "Run the mutant suite")
    assert REUSED in run
    assert 'cp -RL "build/nix-tests-mutants/$MUTANT_SUITE" "build/mutant-accepted/$MUTANT_SUITE"' in run
    save = named_step(job, "Save the report of this accepted derivation")
    condition = re.search(r"\n        if: (.+)", save).group(1)
    assert condition.startswith("success() && ") and REUSED in condition and condition.endswith(ELIGIBLE)
    report = named_step(job, "Retain the mutant suite report")
    assert "build/nix-tests-mutants/" in report and "build/mutant-accepted/" in report
