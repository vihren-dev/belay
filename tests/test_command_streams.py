"""Check how `run_command` (tests/runtime_support.py) streams output and ends a timed-out command."""

import os
from pathlib import Path
import sys

import pytest

from tests.runtime_support import CommandTimeout, run_command

pytestmark = [pytest.mark.integration, pytest.mark.environment]


class MarkerStream:
    """A stand-in for `sys.stdout` that creates a marker file when it receives a given text."""

    def __init__(self, marker: Path, trigger: str) -> None:
        """Remember where the marker goes and which text creates it."""
        self.marker = marker
        self.trigger = trigger
        self.text: list[str] = []

    def write(self, text: str) -> int:
        """Keep `text`; create the marker when the trigger text arrives."""
        self.text.append(text)
        if self.trigger in "".join(self.text):
            self.marker.touch()
        return len(text)

    def flush(self) -> None:
        """Nothing is buffered."""


def test_echo_copies_output_while_the_command_runs(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """`run_command(echo=True)` copies each line to `sys.stdout` when the command writes it.

    CI relies on this to show a long phase in the Actions log while it runs. The command
    writes "first" and then waits until the parent's stream has received it, which only
    a streaming runner can satisfy before the command exits.
    """
    marker = tmp_path / "marker"
    stream = MarkerStream(marker, "first\n")
    monkeypatch.setattr(sys, "stdout", stream)
    program = ("import time\nfrom pathlib import Path\n"
               "print('first', flush=True)\n"
               "deadline = time.monotonic() + 10\n"
               "while not Path('marker').exists() and time.monotonic() < deadline:\n"
               "    time.sleep(0.01)\n"
               "print('seen' if Path('marker').exists() else 'not seen', flush=True)\n")
    result = run_command([sys.executable, "-c", program], cwd=tmp_path, timeout=20, echo=True)
    assert result.returncode == 0, result.diagnostic()
    assert result.stdout == "first\nseen\n"
    assert "".join(stream.text) == result.stdout


def test_timeout_keeps_output_when_a_process_outside_the_group_holds_the_pipes(tmp_path: Path) -> None:
    """A timed-out `run_command` returns the output read before the deadline and a note.

    A grandchild in its own session survives the process-group kill and holds the
    pipes, as `timeout` without `--foreground` did in CI. The runner must not wait
    for it, and must not discard the output that it already read.
    """
    program = ("import subprocess,sys,time\nfrom pathlib import Path\n"
               "holder=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)'],start_new_session=True)\n"
               "Path('holder.pid').write_text(str(holder.pid))\n"
               "print('before deadline',flush=True)\nprint('error line',file=sys.stderr,flush=True)\n"
               "time.sleep(60)\n")
    try:
        with pytest.raises(CommandTimeout) as failure:
            run_command([sys.executable, "-c", program], cwd=tmp_path, timeout=1)
        result = failure.value.result
        assert result.timed_out and result.elapsed < 1 + 5 + 3
        assert result.stdout == "before deadline\n"
        assert result.stderr.startswith("error line\n")
        assert "a process outside the killed process group kept the output pipes open" in result.stderr
    finally:
        holder = tmp_path / "holder.pid"
        if holder.exists():
            try:
                os.kill(int(holder.read_text()), 9)
            except ProcessLookupError:
                pass
