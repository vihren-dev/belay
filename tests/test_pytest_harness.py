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

