"""Bound commands and retain raw output so conclusions can be independently checked."""

from collections.abc import Mapping, Sequence
import json
import os
from pathlib import Path
import subprocess
import time


def write_json(path: Path, value: object) -> None:
    """Write readable evidence without depending on a database or uploader."""
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def run(directory: Path, label: str, command: Sequence[str], *, cwd: Path,
        environment: Mapping[str, str] | None = None, expected: int | None = 0,
        timeout: int = 60) -> subprocess.CompletedProcess[str]:
    """Save exit status, wall time and streams, then check the expected outcome."""
    started = time.monotonic()
    result = subprocess.run(command, cwd=cwd, env={**os.environ, **(environment or {})},
                            capture_output=True, text=True, timeout=timeout)
    (directory / f"{label}.stdout").write_text(result.stdout)
    (directory / f"{label}.stderr").write_text(result.stderr)
    write_json(directory / f"{label}.command.json", {
        "command": list(command), "cwd": str(cwd), "exit": result.returncode,
        "elapsed_seconds": time.monotonic() - started})
    assert expected is None or result.returncode == expected, (
        label, result.returncode, result.stdout[-3000:], result.stderr[-3000:])
    return result
