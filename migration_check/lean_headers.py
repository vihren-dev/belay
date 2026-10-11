"""Read Lean import headers with the pinned compiler, once per distinct source text.

Discovery reads the header of every module, and each compile reads it again to
build its search path. Each `lean --deps-json` process costs about 40-65 ms.
The pinned Lean still parses every header, also on the trusted side: this
module only keeps each result for the life of the process and reads several
headers in one process.
"""

from collections.abc import Callable, Iterable
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

HeaderKey = tuple[Path, Path, Path, str]
"""Toolchain, both libraries and the SHA-256 digest of the source bytes."""


@dataclass(frozen=True)
class HeaderRecord:
    """One `lean --deps-json` record and the file name that Lean read it from."""

    record: object
    path: str


HEADER_RECORDS: dict[HeaderKey, HeaderRecord] = {}
"""Header records of this process. The same bytes give the same header with the same toolchain."""

ReadHeaders = Callable[[list[Path]], str]
"""Run `lean --deps-json` on the given files with a private output directory and return its output."""


def header_key(contents: bytes, sysroot: Path, libraries: tuple[Path, Path]) -> HeaderKey:
    """Identify one header result by toolchain, libraries and exact source bytes."""
    return sysroot, *libraries, hashlib.sha256(contents).hexdigest()


def read_headers(contents: Iterable[bytes], sysroot: Path, libraries: tuple[Path, Path],
                 workspace: Path, run: ReadHeaders) -> None:
    """Read all headers that are not known yet with one `lean --deps-json` process.

    Lean returns one record for each file, in argument order. When the batch
    fails as a whole, for example at its deadline, nothing is stored;
    `known_imports` then reads each file alone, with the error of that file.
    """
    pending: dict[HeaderKey, bytes] = {}
    for text in contents:
        key = header_key(text, sysroot, libraries)
        if key not in HEADER_RECORDS:
            pending.setdefault(key, text)
    if len(pending) < 2:
        return
    with TemporaryDirectory(prefix="headers-", dir=workspace) as temporary:
        directory = Path(temporary).resolve()
        files = [directory / f"{index}.lean" for index in range(len(pending))]
        for path, text in zip(files, pending.values(), strict=True):
            path.write_bytes(text)
        try:
            parsed: object = json.loads(run(files))
        except (RuntimeError, ValueError, OSError, subprocess.SubprocessError):
            return
    records = parsed.get("imports") if isinstance(parsed, dict) else None
    if isinstance(records, list) and len(records) == len(files):
        for key, record, path in zip(pending, records, files, strict=True):
            HEADER_RECORDS[key] = HeaderRecord(record, str(path))


def known_imports(source: Path, sysroot: Path, libraries: tuple[Path, Path],
                  run: ReadHeaders) -> tuple[str, ...]:
    """Give the imports of `source`, reading its header with Lean only when the bytes are new.

    A header error names `source`, also when Lean read a temporary copy.
    """
    key = header_key(source.read_bytes(), sysroot, libraries)
    if key not in HEADER_RECORDS:
        parsed: object = json.loads(run([source]))
        if not isinstance(parsed, dict) or not isinstance(parsed.get("imports"), list):
            raise ValueError("Invalid dependency JSON from pinned Lean")
        if len(parsed["imports"]) != 1:
            raise ValueError("Expected exactly one Lean dependency result")
        HEADER_RECORDS[key] = HeaderRecord(parsed["imports"][0], str(source))
    stored = HEADER_RECORDS[key]
    record = stored.record
    if not isinstance(record, dict):
        raise ValueError("Expected exactly one Lean dependency result")
    if record.get("errors"):
        errors = [str(error).replace(stored.path, str(source)) for error in record["errors"]]
        raise ValueError(f"Invalid Lean import header: {errors}")
    result = record.get("result")
    if not isinstance(result, dict) or not isinstance(result.get("imports"), list):
        raise ValueError("Missing Lean import list")
    names: list[str] = []
    for entry in result["imports"]:
        if not isinstance(entry, dict) or not isinstance(entry.get("module"), str):
            raise ValueError("Invalid Lean import name")
        names.append(entry["module"])
    return tuple(dict.fromkeys(names))
