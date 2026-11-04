"""Export stopped builder reports in bounded frames and recover them from Nix build logs."""

import base64
from collections.abc import Iterable
import json
from pathlib import Path
import tempfile
from uuid import UUID

from tools.observability_records import diagnostic, encode, json_object
from tools.observability_spool import import_execution, spool

PREFIX = "BELAY_REPORT "
"""Each frame carries its identity and byte offset so interleaved builder logs remain distinct."""
FILES = {"execution.json", "report.jsonl"}
"""Only these two data files can cross the build-log boundary."""


def export_reports(directory: Path) -> None:
    """Print complete files in 24 KiB chunks after the producer has stopped."""
    for manifest in sorted(directory.glob("*/execution.json")):
        identity = str(UUID(manifest.parent.name))
        for name in sorted(FILES):
            path = manifest.parent / name
            if not path.exists():
                continue
            with path.open("rb") as stream:
                offset = 0
                while chunk := stream.read(24576):
                    print(PREFIX + encode({"id": identity, "file": name, "offset": offset,
                                           "data": base64.b64encode(chunk).decode()}), flush=True)
                    offset += len(chunk)


def recover(lines: Iterable[str], destination: Path) -> None:
    """Recover ordered contiguous bytes as data; reject invalid paths, offsets and large exports."""
    with tempfile.TemporaryDirectory(prefix="belay-logs-") as temporary:
        root = Path(temporary)
        total = 0
        for line in lines:
            if PREFIX not in line:
                continue
            try:
                frame = json_object(line.split(PREFIX, 1)[1])
                identity = str(UUID(str(frame["id"])))
                name = frame["file"]
                offset = frame["offset"]
                if name not in FILES or not isinstance(offset, int) or offset < 0:
                    raise ValueError("invalid file or offset")
                data = base64.b64decode(str(frame["data"]), validate=True)
                total += len(data)
                if len(data) > 24576 or total > 256 * 1024 * 1024:
                    raise ValueError("build log export exceeds size limit")
                folder = root / identity
                folder.mkdir(exist_ok=True)
                path = folder / str(name)
                length = path.stat().st_size if path.exists() else 0
                if offset < length:
                    with path.open("rb") as stream:
                        stream.seek(offset)
                        if stream.read(len(data)) == data:
                            continue  # Nix repeats a failed builder's last lines in its error summary.
                    raise ValueError("conflicting repeated frame")
                if offset != length:
                    raise ValueError("missing or repeated frame")
                with path.open("ab") as stream:
                    stream.write(data)
            except (ValueError, KeyError, TypeError, OSError) as error:
                diagnostic(f"cannot recover build-log frame ({type(error).__name__})")
                return
        for folder in root.iterdir():
            try:
                if (folder / "report.jsonl").exists():
                    import_execution(folder, destination)
            except (OSError, ValueError, KeyError) as error:
                diagnostic(f"cannot recover {folder.name} ({type(error).__name__})")


if __name__ == "__main__":
    export_reports(spool())
