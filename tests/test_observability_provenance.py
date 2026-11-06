"""The provenance that the host Nix wrapper adds to the executions that it runs (#332).

`tools.observability_provenance` reads an allowlist of GitHub Actions variables and, locally,
the jj working copy. `tools.observability_nix` adds the values when it imports an execution
whose builder ran during the command, and skips cached executions, whose provenance the
command that built them recorded.
"""

from datetime import datetime, timezone
import json
from pathlib import Path
from uuid import uuid4

import pytest

from tests.observability_support import observation
from tools import observability_nix
from tools.observability_logs import export_reports
from tools.observability_nix import instantiation, run
from tools.observability_provenance import provenance, working_copy
from tools.observability_records import execution

CI = {"GITHUB_ACTIONS": "true", "GITHUB_EVENT_NAME": "push", "GITHUB_SHA": "a" * 40, "GITHUB_RUN_ID": "123",
      "GITHUB_RUN_ATTEMPT": "2", "GITHUB_JOB": "check", "GITHUB_TOKEN": "secret", "HOME": "/home/runner"}
"""A GitHub Actions environment with variables outside the allowlist."""


@pytest.mark.unit
def test_ci_environment_gives_the_allowlisted_fields() -> None:
    """On GitHub Actions the metadata holds the event, platform, commit, run, attempt and job, and
    no other variable; jj is not asked."""
    assert provenance(CI, local_commit=lambda: pytest.fail("jj was asked on CI"), host=("arm64", "Darwin")) == {
        "event": "push", "platform": "aarch64-darwin", "commit": "a" * 40, "run_id": "123",
        "run_attempt": "2", "job": "check"}


@pytest.mark.unit
def test_a_missing_ci_variable_stays_absent() -> None:
    """A CI variable that is not set is absent, not empty or guessed."""
    environment = {name: value for name, value in CI.items() if name != "GITHUB_JOB"}
    assert "job" not in provenance(environment, host=("x86_64", "Linux"))


@pytest.mark.unit
def test_local_environment_gives_local_and_the_jj_snapshot() -> None:
    """Outside GitHub Actions the event is `local`, with the commit and change from jj."""
    assert provenance({}, local_commit=lambda: {"commit": "c" * 40, "change": "k" * 32},
                      host=("x86_64", "Linux")) == {
        "event": "local", "platform": "x86_64-linux", "commit": "c" * 40, "change": "k" * 32}


@pytest.mark.unit
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


@pytest.mark.unit
def test_wrapper_imports_only_executions_that_ran_during_the_command(
        tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """An execution that started before the command is skipped; one that started during it is
    imported with the provenance and the suite name of its output."""
    store = tmp_path / "store"
    monkeypatch.setattr(observability_nix, "STORE", f"{store}/")
    since = datetime(2026, 11, 6, 12, 0, tzinfo=timezone.utc)
    cached = output(store, "model", "2026-11-06T11:59:59.999999+00:00")
    fresh = output(store, "functionMutants", "2026-11-06T12:00:00+00:00")
    observability_nix.collect_outputs(f"{store / 'farm'}\n", tmp_path / "spool", since, {"event": "local"})
    assert not (tmp_path / "spool" / cached.name).exists()
    assert execution(tmp_path / "spool" / fresh.name)["metadata"] == '{"event":"local","suite":"functionMutants"}'
    assert json.loads((fresh / "execution.json").read_text())["metadata"] == {}


@pytest.mark.unit
def test_a_recovered_execution_keeps_the_copy_from_its_output(
        tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]) -> None:
    """On macOS a failed builder's output stays visible, so `collect_outputs` imports its execution
    with the suite name before `recover_logs` reads the same execution from the build log. The
    second import keeps the first copy instead of raising a conflict (#348)."""
    store = tmp_path / "store"
    monkeypatch.setattr(observability_nix, "STORE", f"{store}/")
    failed = output(store, "valueMutants", "2026-11-06T12:00:00+00:00")
    export_reports(failed.parent)
    frames = capsys.readouterr().out.splitlines()
    spool = tmp_path / "spool"
    observability_nix.collect_outputs(f"{store / 'farm'}\n", spool, datetime(2026, 11, 6, 12, 0, tzinfo=timezone.utc),
                                      {"event": "push"})
    observability_nix.recover_logs(frames, spool, {"event": "push"})
    assert execution(spool / failed.name)["metadata"] == '{"event":"push","suite":"valueMutants"}'
    assert "cannot recover" not in capsys.readouterr().err


@pytest.mark.unit
def test_instantiation_drops_only_the_output_links() -> None:
    """The derivations of a failed `nix-build` command come from the same file, attribute and options."""
    assert instantiation(["nix-build", "default.nix", "-A", "testReports", "--out-link", "build/t",
                          "--option", "sandbox", "true", "--no-out-link"]) == [
        "nix-instantiate", "default.nix", "-A", "testReports", "--option", "sandbox", "true"]
    assert instantiation(["python3", "-c", "pass"]) is None


ROOT = Path(__file__).resolve().parents[1]
FARM = """let pkgs = import LOCKED {}; in pkgs.linkFarm "farm-ID" [
  { name = "passed"; path = pkgs.runCommand "passed-ID" {} ''
      mkdir -p $out/observability/ID
      printf '{"execution_id":"ID","started_at":"%s","metadata":{}}' "$(date -u +%Y-%m-%dT%H:%M:%S.%6N+00:00)" \\
        > $out/observability/ID/execution.json
      echo '{"$report_type":"SessionFinish","exitstatus":0}' > $out/observability/ID/report.jsonl
    ''; }
  { name = "failed"; path = pkgs.runCommand "failed-ID" {} "sleep 3; exit 1"; }
]
"""
"""A link farm of a suite that passes and a suite that fails; ID makes each test build new."""


@pytest.mark.integration
@pytest.mark.environment
@pytest.mark.requires_nix
@pytest.mark.timeout(120)
def test_a_failed_link_farm_imports_the_suites_that_passed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """When one suite of a link farm fails, `nix-build` prints no path; the wrapper still imports
    the execution of the suite that passed during the command, with the provenance."""
    identity = str(uuid4())
    expression = tmp_path / "farm.nix"
    expression.write_text(FARM.replace("LOCKED", str(ROOT / "build-support/locked-nixpkgs.nix")).replace("ID", identity))
    monkeypatch.setenv("BELAY_OBSERVABILITY_SPOOL", str(tmp_path / "spool"))
    monkeypatch.delenv("BELAY_CLICKHOUSE_URL", raising=False)
    monkeypatch.setattr(observability_nix, "provenance", lambda environment: {"event": "local"})
    assert run(["nix-build", str(expression), "--no-out-link", "--option", "keep-going", "true",
                "--extra-experimental-features", "nix-command flakes"], 100) != 0
    assert execution(tmp_path / "spool" / identity)["metadata"] == '{"event":"local"}'
