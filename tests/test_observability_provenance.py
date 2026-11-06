"""The provenance that the host Nix wrapper adds to the executions that it runs (#332).

`tools.observability_provenance` reads an allowlist of GitHub Actions variables and, locally,
the jj working copy. `tools.observability_nix` adds the values when it imports an execution
whose builder ran during the command, and skips cached executions, whose provenance the
command that built them recorded.
"""

from datetime import datetime, timezone
import json
from pathlib import Path

import pytest

from tests.observability_support import observation
from tools import observability_nix
from tools.observability_provenance import provenance, working_copy
from tools.observability_records import execution

pytestmark = [pytest.mark.unit]
CI = {"GITHUB_ACTIONS": "true", "GITHUB_EVENT_NAME": "push", "GITHUB_SHA": "a" * 40, "GITHUB_RUN_ID": "123",
      "GITHUB_RUN_ATTEMPT": "2", "GITHUB_JOB": "check", "GITHUB_TOKEN": "secret", "HOME": "/home/runner"}
"""A GitHub Actions environment with variables outside the allowlist."""


def test_ci_environment_gives_the_allowlisted_fields() -> None:
    """On GitHub Actions the metadata holds the event, platform, commit, run, attempt and job, and
    no other variable; jj is not asked."""
    assert provenance(CI, local_commit=lambda: pytest.fail("jj was asked on CI"), host=("arm64", "Darwin")) == {
        "event": "push", "platform": "aarch64-darwin", "commit": "a" * 40, "run_id": "123",
        "run_attempt": "2", "job": "check"}


def test_a_missing_ci_variable_stays_absent() -> None:
    """A CI variable that is not set is absent, not empty or guessed."""
    environment = {name: value for name, value in CI.items() if name != "GITHUB_JOB"}
    assert "job" not in provenance(environment, host=("x86_64", "Linux"))


def test_local_environment_gives_local_and_the_jj_snapshot() -> None:
    """Outside GitHub Actions the event is `local`, with the commit and change from jj."""
    assert provenance({}, local_commit=lambda: {"commit": "c" * 40, "change": "k" * 32},
                      host=("x86_64", "Linux")) == {
        "event": "local", "platform": "x86_64-linux", "commit": "c" * 40, "change": "k" * 32}


def test_missing_jj_leaves_the_commit_absent(monkeypatch: pytest.MonkeyPatch) -> None:
    """Without a jj on the path, the local metadata has no commit or change."""
    monkeypatch.setenv("PATH", "")
    assert working_copy() == {}
    assert set(provenance({}, host=("x86_64", "Linux"))) == {"event", "platform"}


def output(store: Path, suite: str, started: str) -> Path:
    """A Nix suite output with one execution that started at `started`, linked from a link farm."""
    folder = store / f"{'0' * 32}-sqlite-verifier-test-{suite}-1"
    directory = observation(folder / "observability")
    manifest = json.loads((directory / "execution.json").read_text())
    (directory / "execution.json").write_text(json.dumps({**manifest, "started_at": started}))
    (store / "farm").mkdir(exist_ok=True)
    (store / "farm" / suite).symlink_to(folder)
    return directory


def test_wrapper_imports_only_executions_that_ran_during_the_command(
        tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """An execution that started before the command is skipped; one that started during it is
    imported with the provenance and the suite name of its output."""
    store = tmp_path / "store"
    monkeypatch.setattr(observability_nix, "STORE", f"{store}/")
    since = datetime.now(timezone.utc)
    cached = output(store, "model", "2026-11-04T12:00:00.123456+00:00")
    fresh = output(store, "functionMutants", datetime.now(timezone.utc).isoformat())
    observability_nix.collect_outputs(f"{store / 'farm'}\n", tmp_path / "spool", since, {"event": "local"})
    assert not (tmp_path / "spool" / cached.name).exists()
    assert execution(tmp_path / "spool" / fresh.name)["metadata"] == '{"event":"local","suite":"functionMutants"}'
    assert json.loads((fresh / "execution.json").read_text())["metadata"] == {}
