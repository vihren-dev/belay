"""Tests of `tools.dev_loop`, the local build loop of `just dev-build` and `just dev-verdict`.

The unit tests check the parts that can be wrong without notice: the reduced claims file, the
layout of the local runtime root, the target arguments and the checks before a build. The
`requires_nix` test runs the loop in the shell of `shell.nix`, and skips outside it.
"""

import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

from conformance.predict import RUNNER
from conformance.sql_text import PROGRAM
from tools import dev_loop
from tools.dev_loop import (PACKAGE_TARGETS, DevLoopError, check_ready, make_runtime_root, reduced_claims,
                            resolved_targets, shell_problem, stale_links)

ROOT = Path(__file__).resolve().parents[1]
CLAIMS = json.loads((ROOT / "judge/claims.json").read_text(encoding="utf-8"))
SHELL = {"BELAY_PARSER_LIBRARY": "/nix/store/parser", "LEAN_CC": "/nix/store/lean-cc"}


@pytest.mark.unit
def test_reduced_claims_copy_the_named_claims_and_no_others() -> None:
    """`reduced_claims` keeps the claims of the named corpora unchanged and drops the others,
    so that a local verdict over a subset checks the same claims as the verdict job."""
    reduced = reduced_claims(CLAIMS, ["corpus-v2", "corpus-v1", "corpus-v2"])
    assert set(reduced["corpora"]) == {"corpus-v1", "corpus-v2"}
    assert all(reduced["corpora"][name] == CLAIMS["corpora"][name] for name in reduced["corpora"])
    assert {key: value for key, value in reduced.items() if key != "corpora"} == \
        {key: value for key, value in CLAIMS.items() if key != "corpora"}
    with pytest.raises(DevLoopError, match="no claim for corpus-v999"):
        reduced_claims(CLAIMS, ["corpus-v1", "corpus-v999"])


@pytest.mark.unit
def test_runtime_root_holds_the_programs_where_predict_reads_them(tmp_path: Path) -> None:
    """`make_runtime_root` copies the local translation program and runner to the paths that
    `conformance.sql_text` and `conformance.predict` read, and replaces older copies."""
    packages = tmp_path / "packages"
    for package, target in (("belay-sqlite-text", "belay-sqlite-translate"),
                            ("verifier-conformance", "conformance-runner")):
        program = packages / package / ".lake/build/bin" / target
        program.parent.mkdir(parents=True)
        program.write_text(f"{target} 1\n")
    runtime = tmp_path / "runtime"
    make_runtime_root(runtime, packages)
    (packages / "verifier-conformance/.lake/build/bin/conformance-runner").write_text("conformance-runner 2\n")
    make_runtime_root(runtime, packages)
    assert (runtime / PROGRAM).read_text() == "belay-sqlite-translate 1\n"
    assert (runtime / RUNNER).read_text() == "conformance-runner 2\n"


@pytest.mark.unit
def test_target_arguments_name_packages_and_targets() -> None:
    """`resolved_targets` builds all targets without arguments, a package's targets for
    `PACKAGE`, one target for `PACKAGE/TARGET`, in build order, and refuses other packages."""
    assert resolved_targets([]) == PACKAGE_TARGETS
    assert resolved_targets(["belay", "verifier-conformance/conformance-runner", "belay/Belay"]) == {
        "verifier-conformance": ("conformance-runner",), "belay": ("Belay", "Belay:shared")}
    with pytest.raises(DevLoopError, match="unknown package 'model'"):
        resolved_targets(["model/Belay.Sqlite.Model"])


@pytest.mark.unit
def test_checks_before_a_build_name_the_next_step(tmp_path: Path) -> None:
    """`check_ready` refuses an environment without the variables of `shell.nix` (`LEAN_CC`
    only on Linux) and a `.lake/build` link into the store, and says what to do."""
    assert shell_problem(SHELL, linux=True) is None
    assert shell_problem({"BELAY_PARSER_LIBRARY": "/nix/store/parser"}, linux=False) is None
    message = shell_problem({"BELAY_PARSER_LIBRARY": "/nix/store/parser"}, linux=True)
    assert message and "LEAN_CC is not set" in message and "direnv allow" in message
    with pytest.raises(DevLoopError, match="BELAY_PARSER_LIBRARY is not set"):
        check_ready(tmp_path, {"LEAN_CC": "/nix/store/lean-cc"}, linux=True)
    store = tmp_path / "store-build"
    store.mkdir()
    link = tmp_path / "packages/belay-sqlite-model/.lake/build"
    link.parent.mkdir(parents=True)
    link.symlink_to(store)
    assert stale_links(tmp_path) == [link]
    with pytest.raises(DevLoopError, match=f"rm {link}"):
        check_ready(tmp_path, SHELL, linux=True)


@pytest.mark.unit
def test_a_timeout_stops_the_loop_with_a_message(monkeypatch: pytest.MonkeyPatch,
                                                 capsys: pytest.CaptureFixture[str]) -> None:
    """`dev_loop.main` turns a build that runs out of time into exit code 2 and a message that
    names the command and its time limit, not a traceback."""
    def stuck(*_: object) -> int:
        raise subprocess.TimeoutExpired(["lake", "build", "conformance-runner"], 1800)
    monkeypatch.setattr(dev_loop, "check_ready", lambda *_: None)
    monkeypatch.setattr(dev_loop, "build", stuck)
    assert dev_loop.main(["build"]) == 2
    assert "`lake build conformance-runner` did not finish in 1800 s" in capsys.readouterr().err


def just(*arguments: str, timeout: int) -> subprocess.CompletedProcess[str]:
    """Run a recipe in the repository and keep its output for the assertion messages."""
    return subprocess.run(["just", *arguments], cwd=ROOT, capture_output=True, text=True, timeout=timeout,
                          check=False)


@pytest.mark.requires_nix
def test_local_loop_builds_incrementally_and_runs_the_judge() -> None:
    """In the shell of `shell.nix`: `just dev-build` compiles nothing on a second run, the
    programs it links start (a Lean upgrade that changes the flags of the `LEAN_CC` wrapper
    fails here), and `just dev-verdict` on one small corpus exits with 0."""
    problem = shell_problem(os.environ, sys.platform.startswith("linux"))
    if problem:
        pytest.skip(problem)
    first = just("dev-build", timeout=1200)
    assert first.returncode == 0, first.stdout[-4000:] + first.stderr[-4000:]
    second = just("dev-build", timeout=300)
    assert second.returncode == 0, second.stdout[-4000:] + second.stderr[-4000:]
    assert "Built " not in second.stdout, second.stdout[-4000:]
    for package, target in (("belay-sqlite-text", "belay-sqlite-translate"),
                            ("verifier-conformance", "conformance-runner")):
        program = ROOT / "packages" / package / ".lake/build/bin" / target
        started = subprocess.run([str(program)], input="", capture_output=True, text=True, timeout=60, check=False)
        assert started.returncode == 0, f"{program}: {started.returncode} {started.stderr[-2000:]}"
    judged = just("dev-verdict", "corpus-v10", timeout=600)
    assert judged.returncode == 0, judged.stdout[-4000:] + judged.stderr[-4000:]
