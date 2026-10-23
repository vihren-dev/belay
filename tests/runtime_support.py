"""Bound test and CI commands and retain diagnostics without altering production isolation."""

import codecs
from collections.abc import Mapping, Sequence
from dataclasses import asdict, dataclass
import json
import os
from pathlib import Path
import selectors
import signal
import subprocess
import sys
from time import monotonic


@dataclass(frozen=True)
class CommandResult:
    """A complete command observation suitable for assertions and failure messages."""

    command: tuple[str, ...]
    returncode: int
    stdout: str
    stderr: str
    elapsed: float
    timed_out: bool = False

    def diagnostic(self) -> str:
        """Keep malformed output as useful as a normal assertion failure."""
        return json.dumps(asdict(self), indent=2, ensure_ascii=False)

    def json_object(self) -> dict[str, object]:
        """Decode an object or fail with both original streams and command context."""
        try:
            value = json.loads(self.stdout)
        except ValueError as error:
            raise AssertionError(f"Invalid command JSON: {self.diagnostic()}") from error
        if not isinstance(value, dict):
            raise AssertionError(f"Expected JSON object: {self.diagnostic()}")
        return value


class CommandTimeout(AssertionError):
    """Expose the partial observation of a command killed at its deadline."""

    def __init__(self, result: CommandResult) -> None:
        """Retain the observation for callers as well as readable failures."""
        self.result = result
        super().__init__(f"Command timed out: {result.diagnostic()}")


PIPE_GRACE_SECONDS = 5
"""How long the pipes of a timed-out command may stay open after its process group is killed."""
OPEN_PIPES_NOTE = ("\nThe output is incomplete: a process outside the killed process group kept "
                   "the output pipes open.\n")
"""Appended to stderr when the grace period ends before the pipes close."""


class CommandStreams:
    """Read a command's stdout and stderr in one thread and keep everything that arrives.

    One thread reads both pipes, so a deadline never needs to stop another thread that
    is blocked on a read. With `echo`, each piece of text goes to this process's stream
    of the same name when it arrives, so a CI log shows a long command while it runs.
    """

    def __init__(self, process: subprocess.Popen[bytes], echo: bool) -> None:
        """Register both pipes of `process`; the text is decoded as UTF-8 with replacement."""
        self.echo = echo
        self.text: dict[str, list[str]] = {"stdout": [], "stderr": []}
        self.selector = selectors.DefaultSelector()
        for name, stream in (("stdout", process.stdout), ("stderr", process.stderr)):
            assert stream is not None
            decoder = codecs.getincrementaldecoder("utf-8")(errors="replace")
            self.selector.register(stream.fileno(), selectors.EVENT_READ, (name, decoder))

    def read_until(self, deadline: float) -> bool:
        """Read until both pipes close (True) or the monotonic `deadline` passes (False)."""
        while self.selector.get_map():
            remaining = deadline - monotonic()
            if remaining <= 0:
                return False
            for key, _ in self.selector.select(remaining):
                name, decoder = key.data
                data = os.read(key.fd, 65536)
                self.keep(name, decoder.decode(data, final=not data))
                if not data:
                    self.selector.unregister(key.fd)
        return True

    def keep(self, name: str, text: str) -> None:
        """Store `text` and, with echo, copy it to `sys.stdout` or `sys.stderr` at once."""
        if not text:
            return
        self.text[name].append(text)
        if self.echo:
            sink = getattr(sys, name)
            sink.write(text)
            sink.flush()

    def close(self) -> tuple[str, str]:
        """Stop reading and return the stdout and stderr text read so far."""
        self.selector.close()
        return "".join(self.text["stdout"]), "".join(self.text["stderr"])


def run_command(arguments: Sequence[str], *, cwd: Path, timeout: float,
                environment: Mapping[str, str] | None = None,
                artifacts: Path | None = None, echo: bool = False) -> CommandResult:
    """Capture a bounded command; on timeout kill its process group and keep partial output.

    With `echo`, the output also goes to this process's stdout and stderr while the
    command runs. Descendants that start their own session leave the group and are not
    killed; if they keep the pipes open, the result keeps the output read so far and
    says that it is incomplete. Tests run trusted commands, so this is a deadline, not a
    containment boundary.
    """
    if timeout <= 0 or not arguments:
        raise ValueError("A command and a positive timeout are required")
    command = tuple(map(str, arguments))
    started = monotonic()
    deadline = started + timeout
    with subprocess.Popen(command, cwd=cwd, env=environment, stdin=subprocess.DEVNULL,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          start_new_session=True) as process:
        streams = CommandStreams(process, echo)
        closed = streams.read_until(deadline)
        timed_out = not closed
        if closed:
            try:
                process.wait(timeout=max(0.0, deadline - monotonic()))
            except subprocess.TimeoutExpired:
                timed_out = True
        if timed_out:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            closed = streams.read_until(monotonic() + PIPE_GRACE_SECONDS)
            process.wait()
        stdout, stderr = streams.close()
    if not closed:
        stderr += OPEN_PIPES_NOTE
    result = CommandResult(command, process.returncode, stdout, stderr,
                           monotonic() - started, timed_out)
    if artifacts is not None:
        artifacts.mkdir(parents=True, exist_ok=True)
        output = artifacts / f"command-{len(list(artifacts.glob('command-*.json'))):04d}.json"
        output.write_text(result.diagnostic() + "\n", encoding="utf-8")
    if timed_out:
        raise CommandTimeout(result)
    return result
