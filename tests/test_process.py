"""Check bounded execution independently of any OS isolation mechanism."""

import os
from pathlib import Path
import subprocess
import sys
import time

import pytest

from migration_check.process import exited_before, run_process

pytestmark = [pytest.mark.integration, pytest.mark.environment]


def test_output_limit(tmp_path: Path) -> None:
    """A noisy child cannot grow its output file or returned diagnostics without bound."""
    result = run_process([sys.executable, '-I', '-c', "import sys; sys.stdout.write('x' * 20_000_000)"],
                         write_root=tmp_path, environment={}, timeout=5)
    assert result.returncode != 0
    assert len(result.stdout) == 1024 * 1024


def test_timeout(tmp_path: Path) -> None:
    """A nonterminating child is stopped by the process deadline."""
    with pytest.raises(subprocess.TimeoutExpired):
        run_process([sys.executable, '-I', '-c', 'while True: pass'],
                    write_root=tmp_path, environment={}, timeout=0.5)


def test_explicit_environment(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Only explicit Lean settings reach the child, in the requested working directory."""
    monkeypatch.setenv('LEAN_PATH', 'ambient-path')
    result = run_process([sys.executable, '-I', '-c',
                          'import os; print(os.getcwd()); print(os.environ["LEAN_PATH"])'],
                         write_root=tmp_path, environment={'LEAN_PATH': 'selected-path'}, timeout=5)
    assert result.returncode == 0
    assert result.stdout.splitlines() == [str(tmp_path.resolve()), 'selected-path']


@pytest.mark.skipif(not hasattr(os, 'pidfd_open'), reason='the polling wait remains without pidfd support')
def test_wait_does_not_poll(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """`run_process` reaps the child only after it exits, with no polling wait.

    `Popen.wait(timeout=...)` polls with sleeps of up to 50 ms;
    `migration_check.process.exited_before` waits for the exit instead.
    """
    timeouts: list[float | None] = []
    original = subprocess.Popen.wait

    def recorded(process: subprocess.Popen[bytes], timeout: float | None = None) -> int:
        """Record the timeout of each wait and run the real wait."""
        timeouts.append(timeout)
        return original(process, timeout)

    monkeypatch.setattr(subprocess.Popen, 'wait', recorded)
    result = run_process([sys.executable, '-I', '-c', 'pass'], write_root=tmp_path, environment={}, timeout=5)
    assert result.returncode == 0
    assert timeouts and all(timeout is None for timeout in timeouts)


@pytest.mark.skipif(not hasattr(os, 'pidfd_open'), reason='the polling wait remains without pidfd support')
def test_exit_is_seen_without_reaping(tmp_path: Path) -> None:
    """`exited_before` reports the exit and leaves the child for `Popen.wait` to reap.

    The deadline kill relies on this: the group ID of an unreaped child cannot be reused.
    """
    with subprocess.Popen([sys.executable, '-I', '-c', 'pass'], cwd=tmp_path) as process:
        assert exited_before(process.pid, 30) is True
        assert process.returncode is None and os.waitpid(process.pid, os.WNOHANG)[0] == process.pid


def test_deadline_kills_the_process_group(tmp_path: Path) -> None:
    """At the deadline `run_process` kills the child's whole group, including its own children."""
    marker = tmp_path / 'grandchild-survived'
    grandchild = f"import pathlib, time; time.sleep(1.5); pathlib.Path({str(marker)!r}).touch()"
    child = f"import subprocess, sys, time; subprocess.Popen([sys.executable, '-I', '-c', {grandchild!r}]); time.sleep(60)"
    with pytest.raises(subprocess.TimeoutExpired):
        run_process([sys.executable, '-I', '-c', child], write_root=tmp_path, environment={}, timeout=0.5)
    time.sleep(2)
    assert not marker.exists()
