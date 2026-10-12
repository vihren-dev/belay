"""Bound trusted Lean processes; OS isolation is the caller's responsibility."""

from collections.abc import Mapping, Sequence
import os
from pathlib import Path
import resource
import signal
import select
import subprocess
from tempfile import TemporaryFile


ALLOWED_ENVIRONMENT = frozenset({"LEAN_PATH", "LEAN_SYSROOT", "LAKE_CACHE_DIR"})
"""Variables a caller may pass: Lean's search path and sysroot, and Lake's artifact cache (ADR 0010)."""


def limit_output_files() -> None:
    """Bound each produced file, including captured output streams."""
    resource.setrlimit(resource.RLIMIT_FSIZE, (16 * 1024 * 1024, 16 * 1024 * 1024))


def exited_before(pid: int, timeout: float) -> bool | None:
    """Wait until the child exits or the deadline passes, without reaping the child.

    The child stays a zombie until `Popen.wait` reaps it, so its process-group
    ID cannot be reused while the caller decides whether to kill the group.
    Linux uses a pidfd, which becomes readable at the exit, with no polling.
    Returns `None` without pidfd support, for example on macOS.
    """
    if not hasattr(os, "pidfd_open"):
        return None
    try:
        descriptor = os.pidfd_open(pid)
    except OSError:
        return None
    try:
        waiter = select.poll()
        waiter.register(descriptor, select.POLLIN)
        return bool(waiter.poll(timeout * 1000))
    finally:
        os.close(descriptor)


def wait_with_deadline(process: subprocess.Popen[bytes], timeout: float) -> bool:
    """Reap the child; at the deadline, first kill its whole process group.

    `Popen.wait(timeout=...)` polls with sleeps of up to 50 ms, so a short child
    seemed to run up to 50 ms longer. `exited_before` returns at the exit
    instead. Without pidfd support, the polling wait remains.
    Returns false when the deadline killed the process group.
    """
    exited = exited_before(process.pid, timeout)
    if exited is None:
        try:
            process.wait(timeout=timeout)
            return True
        except subprocess.TimeoutExpired:
            exited = False
    if not exited:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    process.wait()
    return exited


def run_process(
    arguments: Sequence[str], *, write_root: Path,
    environment: Mapping[str, str], timeout: float = 30,
) -> subprocess.CompletedProcess[str]:
    """Run trusted source code with explicit environment, deadline and bounded output."""
    if timeout <= 0:
        raise ValueError("A positive process timeout is required")
    if set(environment) - ALLOWED_ENVIRONMENT:
        raise ValueError("Only trusted Lean search-path and Lake cache settings may enter the process")
    command = list(arguments)
    env = {"HOME": str(write_root), "TMPDIR": str(write_root), "LANG": "C.UTF-8"}
    env.update(environment)
    with TemporaryFile(dir=write_root) as stdout_file, TemporaryFile(dir=write_root) as stderr_file:
        with subprocess.Popen(
            command, cwd=write_root, env=env, stdin=subprocess.DEVNULL,
            stdout=stdout_file, stderr=stderr_file, start_new_session=True,
            preexec_fn=limit_output_files,
        ) as process:
            if not wait_with_deadline(process, timeout):
                raise subprocess.TimeoutExpired(command, timeout)
            stdout_file.seek(0)
            stderr_file.seek(0)
            stdout = stdout_file.read(1024 * 1024).decode("utf-8", errors="replace")
            stderr = stderr_file.read(1024 * 1024).decode("utf-8", errors="replace")
            return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
