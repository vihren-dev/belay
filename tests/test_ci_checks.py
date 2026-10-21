"""CI reuses only declared artifacts and always invokes the full fresh host recipe."""

import json
from pathlib import Path
import re
import subprocess
from unittest.mock import patch

import pytest

from tools.ci_checks import CHECKS_PHASE_LIMIT_SECONDS, run_checks
from tests.runtime_support import CommandResult, CommandTimeout

pytestmark = [pytest.mark.unit, pytest.mark.environment]

OWNER_JOB_LIMIT_MINUTES = 75
"""Owner feedback of 2026-10-08 restores the aggregate job ceiling; child deadlines stay independent."""


@pytest.mark.parametrize("scope", ["test", "full"])
@pytest.mark.parametrize("mode", ["source", "build"])
@pytest.mark.parametrize("system", ["aarch64-darwin", "x86_64-linux"])
def test_hosted_job_keeps_owner_limit_and_child_deadlines(
        tmp_path: Path, scope: str, mode: str, system: str) -> None:
    """The 75-minute aggregate limit and individual child deadlines are separate bounds."""
    workflow = (Path(__file__).resolve().parents[1] / ".github/workflows/ci.yml").read_text()
    check_job = workflow.split("  check:\n", 1)[1].split("\n  publish:", 1)[0]
    match = re.search(r"(?m)^    timeout-minutes: ([1-9][0-9]*)$", check_job)
    assert match is not None
    budgets: list[float] = []

    def invoke(command: list[str], *, cwd: Path, environment: dict[str, str],
               timeout: float, artifacts: Path, echo: bool) -> CommandResult:
        """Observe real orchestration limits while replacing only external build and version work."""
        budgets.append(timeout)
        output = str(tmp_path / "runtime") if command[0] == "nix-build" else ""
        return CommandResult(tuple(command), 0, output, "", 0.01)

    with patch("tools.ci_checks.check_resources"), patch("tools.ci_checks.run_command", side_effect=invoke), \
         patch.dict("os.environ", {"SQLITE_VERIFIER_SYSTEM": system}):
        run_checks(scope, mode, system, tmp_path)
    recipes = (Path(__file__).resolve().parents[1] / "justfile").read_text()
    reference = re.search(r"timeout --foreground ([1-9][0-9]*) nix-build [^\n]*-A apiReference", recipes)
    assert reference is not None, "Reference phase has no bounded recipe"
    reference_limit = int(reference.group(1))
    assert int(match.group(1)) == OWNER_JOB_LIMIT_MINUTES
    assert reference_limit == 1800
    assert all(0 < timeout <= OWNER_JOB_LIMIT_MINUTES * 60 for timeout in budgets)
    assert budgets[-1] == CHECKS_PHASE_LIMIT_SECONDS == 3600



@pytest.mark.parametrize("mode", ["source", "build"])
@pytest.mark.parametrize("system", ["aarch64-darwin", "x86_64-linux"])
def test_ci_modes_retain_fresh_checks(tmp_path: Path, mode: str, system: str) -> None:
    """Both modes run the complete host recipes of each scope, the build mode on the conformance runtime."""
    runtime = tmp_path / "runtime"
    (runtime / "build").mkdir(parents=True)
    original_bin = tmp_path / "original-bin"
    original_bin.mkdir()
    (runtime / "lean/bin").mkdir(parents=True)
    for compiler in (original_bin / "clang", runtime / "lean/bin/clang"):
        compiler.write_text("#!/bin/sh\nexit 0\n")
        compiler.chmod(0o755)
    commands: list[list[str]] = []
    environments: list[dict[str, str]] = []
    echoes: list[object] = []

    def run(command: list[str], **options: object) -> CommandResult:
        """Return tiny artifact paths without invoking Nix, compilers or a sandbox."""
        commands.append(command)
        environments.append(dict(options["environment"]))
        echoes.append(options["echo"])
        stdout = str(runtime) if command[0] == "nix-build" else ""
        return CommandResult(tuple(command), 0, stdout, "", 0.01)

    with patch("tools.ci_checks.check_resources"), patch("tools.ci_checks.run_command", side_effect=run), \
         patch.dict("os.environ", {"SQLITE_VERIFIER_SYSTEM": system, "PATH": str(original_bin), "CC": "clang"}, clear=True):
        run_checks("full", mode, system, tmp_path)
        assert commands[-1] == ["just", "test-full", "test-nix", "test-scheduled-checks"]
        run_checks("infrastructure", mode, system, tmp_path)
        assert commands[-1] == ["just", "test-full", "test-nix"]
        run_checks("test", mode, system, tmp_path)
    assert commands[-1] == ["just", "test-full"]
    assert set(echoes) == {True}, "Every phase streams its output to the CI log"
    if mode == "build":
        assert commands[0][3] == "conformance"
        assert environments[-1]["SQLITE_VERIFIER_RUNTIME_ROOT"] == str(runtime)
        assert "SQLITE_VERIFIER_UNIT_CHECKS" not in environments[-1]
        assert environments[-1]["CC"] == "clang"
        assert environments[-1]["PATH"] == str(original_bin)
        assert [str(runtime / "lean/bin/lean"), "--version"] in commands
        assert [str(runtime / "lean/bin/lake"), "--version"] in commands
        assert not (tmp_path / "build/cached-unit").exists()
    else:
        assert commands[0] == ["just", "setup"]
        assert "SQLITE_VERIFIER_UNIT_CHECKS" not in environments[-1]
    assert all(row["exit_code"] == 0 for row in json.loads((tmp_path / "build/ci-phases.json").read_text()))


def test_unknown_scope_is_rejected(tmp_path: Path) -> None:
    """A scope that tests/ci_scope.py does not produce fails before any command runs."""
    with patch("tools.ci_checks.run_command") as run, pytest.raises(ValueError, match="Unknown CI scope"):
        run_checks("docs", "build", "x86_64-linux", tmp_path)
    run.assert_not_called()


def test_ci_failure_retains_phase_status(tmp_path: Path) -> None:
    """A failed host recipe fails the job and still records its duration and status."""
    with patch("tools.ci_checks.check_resources"), \
         patch.dict("os.environ", {"SQLITE_VERIFIER_SYSTEM": "aarch64-darwin"}), \
         patch("tools.ci_checks.run_command", return_value=CommandResult((), 7, "failure stdout", "failure stderr", 0.01)):
        with pytest.raises(subprocess.CalledProcessError):
            run_checks("test", "source", "aarch64-darwin", tmp_path)
    assert json.loads((tmp_path / "build/ci-phases.json").read_text())[0]["exit_code"] == 7


def test_ci_timeout_retains_group_runner_diagnostics(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    """`run_checks` delegates timeout cleanup to the process-group runner and keeps its result.

    The runner already streamed the phase output, so the timeout message names the phase,
    its limit and its artifact folder without printing the output a second time.
    """
    failure = CommandResult(("just", "setup"), -9, "child output", "child error", 0.01, True)
    with patch("tools.ci_checks.check_resources"), \
         patch.dict("os.environ", {"SQLITE_VERIFIER_SYSTEM": "aarch64-darwin"}), \
         patch("tools.ci_checks.run_command", side_effect=CommandTimeout(failure)) as run:
        with pytest.raises(CommandTimeout):
            run_checks("test", "source", "aarch64-darwin", tmp_path)
    assert run.call_args.kwargs["timeout"] == 330
    assert run.call_args.kwargs["artifacts"] == tmp_path / "build/ci-phases/setup"
    assert json.loads((tmp_path / "build/ci-phases.json").read_text())[0]["exit_code"] == -9
    captured = capsys.readouterr()
    assert "Phase setup stopped after its 330-second limit: just setup." in captured.err
    assert "build/ci-phases/setup/" in captured.err
    assert "child output" not in captured.out + captured.err
    assert "child error" not in captured.out + captured.err
