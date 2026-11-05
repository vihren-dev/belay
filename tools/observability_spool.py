"""Own producer locks and immutable copies so upload never races a running pytest."""

from collections.abc import Iterator
from contextlib import contextmanager
import fcntl
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from typing import BinaryIO
from uuid import UUID

from tools.observability_records import diagnostic, execution

ROOT = Path(__file__).resolve().parents[1]
"""The shared setup's checkout, independent of the caller's current directory."""
UPLOAD_SECONDS = 15
"""Hard process deadline, including DNS, response reads, validation and retry scanning."""


def spool() -> Path:
    """Keep local and CI reports in the ignored build directory unless explicitly redirected."""
    return Path(os.environ.get("BELAY_OBSERVABILITY_SPOOL", str(ROOT / "build/observability")))


@contextmanager
def lock(directory: Path) -> Iterator[BinaryIO | None]:
    """Skip active producers and concurrent importers/uploaders using an OS-released lock."""
    with (directory / ".lock").open("ab") as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            yield None
            return
        try:
            yield handle
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)


def import_execution(source: Path, destination: Path) -> None:
    """Publish a complete copy atomically; reject conflicting bytes for an existing identity."""
    identity = str(UUID(str(execution(source)["execution_id"])))
    destination.mkdir(parents=True, exist_ok=True)
    target = destination / identity
    temporary = Path(tempfile.mkdtemp(prefix=".import-", dir=destination))
    try:
        for name in ("execution.json", "report.jsonl"):
            if (source / name).is_symlink():
                raise ValueError("artifact files must not be symlinks")
            shutil.copyfile(source / name, temporary / name)
        try:
            temporary.rename(target)
        except OSError:
            if not target.is_dir():
                raise
            with lock(target) as held:
                if held is None:
                    return
                for name in ("execution.json", "report.jsonl"):
                    if (temporary / name).read_bytes() != (target / name).read_bytes():
                        raise ValueError(f"conflicting observation for {identity}")
    finally:
        if temporary.exists():
            shutil.rmtree(temporary)


def attempt_upload(directory: Path | None = None) -> bool:
    """Run delivery in a killable child; collection and tests retain their own exit status."""
    if os.environ.get("BELAY_OBSERVABILITY_BUILD") == "1":
        return True
    try:
        result = subprocess.run([sys.executable, "-m", "tools.observability_upload",
                                 "--worker", str(directory or spool())], cwd=ROOT,
                                stdin=subprocess.DEVNULL, timeout=UPLOAD_SECONDS)
        if result.returncode:
            diagnostic("upload incomplete; files retained for the next test command")
        return result.returncode == 0
    except (OSError, subprocess.TimeoutExpired) as error:
        diagnostic(f"upload stopped ({type(error).__name__}); files retained for retry")
        return False
