"""Check `migration_check.lean_headers`: each distinct header is read by Lean once per process.

The batch and the cache must give the same imports and the same errors as one
`lean --deps-json` process for each file, because discovery and compile order
depend on them. The last test uses the pinned Lean as the reference.
"""

import json
from pathlib import Path

import pytest

from migration_check import lean_headers
from migration_check.lean_headers import known_imports, read_headers
from migration_check.source_closure import header_reader

pytestmark = [pytest.mark.unit, pytest.mark.environment]
SYSROOT, LIBRARIES = Path("/toolchain"), (Path("/application"), Path("/model"))
HEADERS = {b"import Init\nimport A\n": ["Init", "A"], b"import B\nimport B\n": ["B"], b"def x := 1\n": []}


def record(contents: bytes, path: Path) -> object:
    """Answer like `lean --deps-json` for the known test headers; other bytes have a header error."""
    if contents not in HEADERS:
        return {"errors": [f"{path}:1:0: unexpected token"]}
    return {"errors": [], "result": {"imports": [{"module": name} for name in HEADERS[contents]]}}


@pytest.fixture
def calls(monkeypatch: pytest.MonkeyPatch) -> list[list[Path]]:
    """Start with no known headers and record the files of each simulated Lean process."""
    monkeypatch.setattr(lean_headers, "HEADER_RECORDS", {})
    return []


def runner(calls: list[list[Path]]) -> lean_headers.ReadHeaders:
    """Simulate one Lean process that reads the given files."""
    def run(files: list[Path]) -> str:
        """Record the call and answer one record for each file, in order."""
        calls.append(list(files))
        return json.dumps({"imports": [record(path.read_bytes(), path) for path in files]})
    return run


def sources(tmp_path: Path) -> list[Path]:
    """Write each test header, and one invalid header, to its own file."""
    paths = []
    for index, contents in enumerate([*HEADERS, b"import \xc2\xab\n"]):
        path = tmp_path / f"Module{index}.lean"
        path.write_bytes(contents)
        paths.append(path)
    return paths


def test_batch_reads_all_new_headers_in_one_process(tmp_path: Path, calls: list[list[Path]]) -> None:
    """`read_headers` reads all new headers in one process; `known_imports` then starts none."""
    files = sources(tmp_path)
    read_headers([path.read_bytes() for path in files], SYSROOT, LIBRARIES, tmp_path, runner(calls))
    assert len(calls) == 1 and len(calls[0]) == len(files)
    assert [known_imports(path, SYSROOT, LIBRARIES, runner(calls)) for path in files[:3]] == [
        ("Init", "A"), ("B",), ()]
    assert len(calls) == 1


def test_header_error_names_the_source_file(tmp_path: Path, calls: list[list[Path]]) -> None:
    """`known_imports` names the real source file in an error that Lean reported for a batch copy."""
    files = sources(tmp_path)
    read_headers([path.read_bytes() for path in files], SYSROOT, LIBRARIES, tmp_path, runner(calls))
    with pytest.raises(ValueError) as batched:
        known_imports(files[-1], SYSROOT, LIBRARIES, runner(calls))
    lean_headers.HEADER_RECORDS.clear()
    with pytest.raises(ValueError) as alone:
        known_imports(files[-1], SYSROOT, LIBRARIES, runner(calls))
    assert str(batched.value) == str(alone.value)
    assert f"{files[-1]}:1:0" in str(alone.value)


def test_changed_bytes_are_read_again(tmp_path: Path, calls: list[list[Path]]) -> None:
    """`known_imports` keys results by content: changed bytes at the same path start a new process."""
    path = tmp_path / "Module.lean"
    path.write_bytes(b"def x := 1\n")
    assert known_imports(path, SYSROOT, LIBRARIES, runner(calls)) == ()
    path.write_bytes(b"import Init\nimport A\n")
    assert known_imports(path, SYSROOT, LIBRARIES, runner(calls)) == ("Init", "A")
    assert len(calls) == 2


def test_failed_batch_stores_nothing(tmp_path: Path, calls: list[list[Path]]) -> None:
    """`read_headers` stores nothing when its process fails; `known_imports` then reads each file alone."""
    def failed(files: list[Path]) -> str:
        """Simulate a failed Lean process."""
        calls.append(list(files))
        raise RuntimeError("Lean failed")

    files = sources(tmp_path)
    read_headers([path.read_bytes() for path in files], SYSROOT, LIBRARIES, tmp_path, failed)
    assert not lean_headers.HEADER_RECORDS
    assert known_imports(files[0], SYSROOT, LIBRARIES, runner(calls)) == ("Init", "A")


@pytest.mark.requires_lean
def test_batch_matches_one_process_per_file_with_pinned_lean(tmp_path: Path, lean_sysroot: Path,
        lean_libraries: tuple[Path, Path], monkeypatch: pytest.MonkeyPatch) -> None:
    """With the pinned Lean, `read_headers` batches and single `known_imports` reads give equal results."""
    files = sources(tmp_path)
    run = header_reader(lean_sysroot, lean_libraries, tmp_path)

    def outcomes() -> list[object]:
        """Give each file's imports or error message."""
        results: list[object] = []
        for path in files:
            try:
                results.append(known_imports(path, lean_sysroot, lean_libraries, run))
            except ValueError as error:
                results.append(str(error))
        return results

    monkeypatch.setattr(lean_headers, "HEADER_RECORDS", {})
    alone = outcomes()
    monkeypatch.setattr(lean_headers, "HEADER_RECORDS", {})
    read_headers([path.read_bytes() for path in files], lean_sysroot, lean_libraries, tmp_path, run)
    assert len(lean_headers.HEADER_RECORDS) == len(files)
    assert outcomes() == alone
    assert isinstance(alone[-1], str) and str(files[-1]) in alone[-1]
