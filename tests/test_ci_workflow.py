"""Checks and reference builds share the Linux-only pull-request schedule."""

import re

import pytest

from tests.ci_workflow_text import GUARD, ROOT, job_steps, workflow_jobs

EXPLANATION_STEP = "Skip macOS checks on pull requests"
"""The explanatory step reports the skipped native platform without running it."""
pytestmark = [pytest.mark.unit]


def check_job_steps() -> list[tuple[str, str]]:
    """Name and condition of each step of the check job, so the tests can verify the platform guard."""
    text = (ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8")
    job = text[text.index("\n  check:\n"):text.index("\n  mutants:\n")]
    steps: list[tuple[str, str]] = []
    for block in re.split(r"\n      - ", "\n" + job.split("\n    steps:\n", 1)[1])[1:]:
        name = re.search(r"(?:^|\n\s*)name: (.+)", block)
        uses = re.match(r"uses: (\S+)", block)
        condition = re.search(r"\n        if: (.+)", block) or re.match(r"if: (.+)", block)
        label = name.group(1) if name else (uses.group(1) if uses else block.splitlines()[0])
        steps.append((label.strip(), condition.group(1).strip() if condition else ""))
    return steps


def test_platform_runs_skips_macos_only_on_pull_requests() -> None:
    """Linux runs checks and references; macOS runs them outside pull requests."""
    text = (ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8")
    assert ("PLATFORM_RUNS: ${{ matrix.system == 'x86_64-linux' || "
            "github.event_name != 'pull_request' }}") in text


def test_every_working_step_is_guarded() -> None:
    """Every working step is skipped on macOS pull requests, including reference setup."""
    steps = check_job_steps()
    assert steps, "No steps found in the check job"
    unguarded = [name for name, condition in steps
                 if GUARD not in condition and name != EXPLANATION_STEP]
    assert not unguarded, f"Steps that would run on macOS pull requests: {unguarded}"
    conditions = dict(steps)
    assert conditions[EXPLANATION_STEP] == "env.PLATFORM_RUNS != 'true'"
    reference = "Build checked API reference"
    assert conditions[reference] == GUARD + " && steps.scope.outputs.scope != 'docs'"
    assert conditions["Retain checked API reference"] == "always() && " + conditions[reference]


def test_cache_save_is_limited_to_main_and_nightly() -> None:
    """Pull requests and manual runs can restore caches but cannot publish them."""
    text = (ROOT / ".github/workflows/ci.yml").read_text(encoding="utf-8")
    expected = ("save: ${{ github.event_name == 'schedule' || "
                "(github.event_name == 'push' && github.ref == 'refs/heads/main') }}")
    assert expected in text
    assert "save: true" not in text


CACHE_URL = "https://cache.vihren.dev/sqlite-verifier"
CACHE_KEY = "sqlite-verifier:XgeRqTIGBEw3VP8GPrzSvdU+5t1lJz7uEMhIG1lh7QE="
"""The publicly readable Vihren Attic cache and its signing key."""


def test_check_job_substitutes_from_the_public_cache_with_fallback() -> None:
    """Checks read the Attic cache without credentials; a failed substitution builds locally."""
    check = workflow_jobs()["check"]
    assert f"extra-substituters = {CACHE_URL}" in check
    assert f"extra-trusted-public-keys = {CACHE_KEY}" in check
    assert "fallback = true" in check
    assert "sandbox-fallback = false" in check


def test_only_the_publishing_job_receives_the_write_token() -> None:
    """The check and mutants jobs, which pull requests run, never see the upload token."""
    jobs = workflow_jobs()
    assert set(jobs) == {"check", "mutants", "publish-nix-store"}
    assert "ATTIC_WRITE_TOKEN" not in jobs["check"]
    assert "ATTIC_WRITE_TOKEN" not in jobs["mutants"]
    assert "secrets.ATTIC_WRITE_TOKEN" in jobs["publish-nix-store"]


def test_publishing_follows_accepted_main_and_nightly_checks_only() -> None:
    """Uploads run after the checks of main pushes and nightly runs, also when the check of the
    other platform failed (#327), in the main-only environment, and cannot fail the workflow.
    The upload itself needs the store that a passed check saved (the next tests)."""
    publish = workflow_jobs()["publish-nix-store"]
    assert ("if: ${{ !cancelled() && (github.event_name == 'schedule' || "
            "(github.event_name == 'push' && github.ref == 'refs/heads/main')) }}") in publish
    assert "needs: check" in publish
    assert "environment: attic-publish" in publish
    assert "continue-on-error: true" in publish
    assert re.search(r"\n    timeout-minutes: \d+\n", publish)


def test_publishing_restores_the_check_jobs_store_without_saving() -> None:
    """The publishing job restores exactly the key the check job saved and never writes a GitHub cache."""
    jobs = workflow_jobs()
    key = re.compile(r"primary-key: (.+)")
    assert key.search(jobs["publish-nix-store"]).group(1) == key.search(jobs["check"]).group(1)
    assert "save: false" in jobs["publish-nix-store"]


def test_publishing_uploads_the_restored_store_only_on_an_exact_hit() -> None:
    """The upload runs only after the check job's store was restored, and pushes every non-derivation path."""
    publish = workflow_jobs()["publish-nix-store"]
    upload = publish[publish.index("- name: Upload store paths"):]
    assert "if: steps.restore.outputs.hit-primary-key == 'true'" in upload
    assert "id: restore" in publish[:publish.index("- name: Upload store paths")]
    assert "hit-primary-key == 'true'" not in publish[:publish.index("- name: Upload store paths")]
    assert "--inputs-from path:./nix nixpkgs#attic-client" in upload
    missing = next(step for step in job_steps(publish) if "Report a missing saved store" in step)
    assert "if: steps.restore.outputs.hit-primary-key != 'true'" in missing
    assert 'run: echo "::warning::No saved Nix store' in missing
    assert 'login vihren https://cache.vihren.dev "$ATTIC_WRITE_TOKEN"' in upload
    assert ("nix path-info --all | grep -v '\\.drv$' | "
            '"$attic" push vihren:sqlite-verifier --stdin') in upload


def test_mutant_job_runs_each_mutant_suite_for_the_full_scope() -> None:
    """The mutants job runs each suite of tests/nix_mutant_suites.json on its own runner, only
    for the full scope and with the platform guard of the check job, and never saves a cache."""
    import json
    job = workflow_jobs()["mutants"]
    suites = json.loads((ROOT / "tests/nix_mutant_suites.json").read_text())
    assert f"suite: [{', '.join(suites)}]" in job
    assert "save: false" in job and "save: ${{" not in job
    assert "timeout-minutes: 75" in job
    steps = re.split(r"\n      - ", job.split("\n    steps:\n", 1)[1])
    working = [step for step in steps if "Skip macOS checks" not in step]
    assert all(GUARD in step for step in working)
    full = "steps.scope.outputs.scope == 'full'"
    assert all(full in step for step in working
               if "checkout" not in step and "id: scope" not in step and "id: tree" not in step)
    assert 'just test-mutants "$MUTANT_SUITE"' in job
