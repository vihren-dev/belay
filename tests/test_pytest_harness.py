"""Exercise runtime selection, prerequisites and bounded commands in a minimal pytest repository."""

import os
from pathlib import Path
import shutil
import sys
import time

import pytest

from tests.runtime_support import CommandResult, CommandTimeout, run_command

pytestmark = [pytest.mark.integration, pytest.mark.environment]
ROOT = Path(__file__).resolve().parents[1]
SUPPORT = ("__init__.py", "runtime_fixtures.py", "runtime_support.py")


@pytest.fixture
def harness(tmp_path: Path) -> Path:
    """Copy only test infrastructure so probes cannot accidentally collect the real suites."""
    root = tmp_path / "harness"
    (root / "tests").mkdir(parents=True)
    shutil.copy2(ROOT / "pytest.ini", root)
    shutil.copy2(ROOT / "conftest.py", root)
    for name in SUPPORT:
        shutil.copy2(ROOT / "tests" / name, root / "tests" / name)
    (root / "build-support").mkdir()
    shutil.copy2(ROOT / "build-support/observability-schema.sql", root / "build-support")
    (root / "tools").mkdir()
    for source in [ROOT / "tools/__init__.py", *(ROOT / "tools").glob("observability_*.py")]:
        shutil.copy2(source, root / "tools" / source.name)
    return root


def invoke(root: Path, source: str, *arguments: str, no_tools: bool = False) -> CommandResult:
    """Run a bounded isolated pytest invocation using the same pinned interpreter."""
    (root / "tests/test_probe.py").write_text(source)
    environment = dict(os.environ)
    environment["PYTEST_DISABLE_PLUGIN_AUTOLOAD"] = "1"
    if no_tools:
        environment["PATH"] = str(root / "missing-tools")
    return run_command([sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider", *arguments],
                       cwd=root, timeout=15, environment=environment)


def test_missing_prerequisite_fails_setup(harness: Path) -> None:
    """A selected case whose tools are unavailable errors in setup instead of skipping or running."""
    source = ('import pytest\npytestmark = pytest.mark.requires_lean\n'
              'def test_tool():\n    raise AssertionError("call ran")\n')
    result = invoke(harness, source, no_tools=True)
    assert result.returncode == 1 and "Required Lean compiler is missing" in result.stdout, result.diagnostic()
    assert "1 error" in result.stdout and "call ran" not in result.stdout, result.diagnostic()


def test_command_json_diagnostics_retain_both_streams(tmp_path: Path) -> None:
    """Malformed JSON retains the command, status, stdout, stderr and elapsed time."""
    result = run_command([sys.executable, "-c", "import sys; print('invalid'); print('detail',file=sys.stderr)"],
                         cwd=tmp_path, timeout=5)
    with pytest.raises(AssertionError) as failure:
        result.json_object()
    assert all(value in str(failure.value) for value in ("invalid", "detail", "elapsed", "returncode", sys.executable))


def test_timeout_kills_process_group_and_retains_output(tmp_path: Path) -> None:
    """A timed-out command's group, including a grandchild, is killed and partial output is kept."""
    program = ("import subprocess,sys\nfrom pathlib import Path\n"
               "child=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)'])\n"
               "Path('child.pid').write_text(str(child.pid))\n"
               "print('partial stdout',flush=True)\nprint('partial stderr',file=sys.stderr,flush=True)\n"
               "child.wait()\n")
    with pytest.raises(CommandTimeout) as failure:
        run_command([sys.executable, "-c", program], cwd=tmp_path, timeout=1, artifacts=tmp_path / "evidence")
    result = failure.value.result
    assert result.timed_out and result.returncode != 0 and result.elapsed < 10
    assert "partial stdout" in result.stdout and "partial stderr" in result.stderr
    assert (tmp_path / "evidence/command-0000.json").is_file()
    pid = int((tmp_path / "child.pid").read_text())
    # The killed grandchild is reparented; it may briefly remain a zombie until init reaps it.
    for _ in range(100):
        state = run_command(["ps", "-o", "stat=", "-p", str(pid)], cwd=tmp_path, timeout=2).stdout.strip()
        if not state or state.startswith("Z"):
            break
        time.sleep(0.02)
    else:
        pytest.fail(f"Grandchild {pid} survived the process-group timeout")



FAKE_BASE_BUILD = ('from pathlib import Path\n'
                   'def built_base(repository, lean):\n'
                   '    if (repository / "fail").exists():\n'
                   '        raise RuntimeError("lake build failed in base")\n'
                   '    with (repository / "builds.log").open("a") as log:\n'
                   '        log.write(f"{repository} {lean}\\n")\n')
"""A stand-in for `conformance.mutant_builds`, which logs each base build instead of running Lake."""
MUTANT_PROBE = ('import pytest\nfrom pathlib import Path\npytestmark = pytest.mark.requires_mutant_base\n'
                'def test_first():\n    Path("ran").touch()\n    assert Path("builds.log").is_file()\n'
                'def test_second():\n    assert Path("builds.log").is_file()\n')
"""Mutant measurements that see whether the base was built before they started."""
UNMARKED_PROBE = 'def test_unmarked():\n    pass\n'
"""A test without the mutant marker."""


def with_fake_base_build(harness: Path) -> Path:
    """Add the stand-in base build to a harness."""
    (harness / "conformance").mkdir()
    (harness / "conformance/mutant_builds.py").write_text(FAKE_BASE_BUILD)
    return harness


def test_mutant_tests_start_after_one_base_build(harness: Path) -> None:
    """The collection hook of `tests/runtime_fixtures.py` builds the mutant base once, with the
    repository and the runtime's `lean` folder, before the first marked test starts (#346), so
    no test's own time limit pays for the build."""
    root = with_fake_base_build(harness)
    result = invoke(root, MUTANT_PROBE)
    assert result.returncode == 0 and "2 passed" in result.stdout, result.diagnostic()
    assert (root / "builds.log").read_text() == f"{root.resolve()} {root.resolve() / 'lean'}\n"


def test_no_base_build_without_a_selected_mutant_test(harness: Path) -> None:
    """The hook builds nothing when the selection has no marked test, when `-k` deselects the
    marked tests (exit status 5, no tests ran), or when pytest only collects tests."""
    root = with_fake_base_build(harness)
    for source, arguments in ((UNMARKED_PROBE, ()), (MUTANT_PROBE, ("-k", "nothing")), (MUTANT_PROBE, ("--collect-only",))):
        result = invoke(root, source, *arguments)
        assert result.returncode in (0, 5), result.diagnostic()
    assert not (root / "builds.log").exists()


def test_failed_base_build_stops_the_session(harness: Path) -> None:
    """A failed base build stops the session with its error before any marked test runs."""
    root = with_fake_base_build(harness)
    (root / "fail").touch()
    result = invoke(root, MUTANT_PROBE)
    assert result.returncode == 1, result.diagnostic()
    assert "The unchanged model of the mutant tests did not build: lake build failed in base" in result.stdout + result.stderr
    assert not (root / "ran").exists(), result.diagnostic()
