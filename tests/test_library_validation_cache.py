"""Check that `migration_check.runtime.validate_libraries` scans each set of roots once per process.

One command checks the same installed libraries up to three times. A scan reads
every `.olean` file, so the verifier remembers a successful scan. A refused
scan is not remembered.
"""

from collections.abc import Iterator
from pathlib import Path

import pytest

from migration_check import runtime
from migration_check.runtime import validate_libraries

pytestmark = [pytest.mark.unit, pytest.mark.environment]


def roots(base: Path, *, conflict: bool = False) -> tuple[Path, tuple[Path, Path]]:
    """Make a sysroot and two libraries; with `conflict`, two of them install the same module."""
    sysroot, first, second = base / "sysroot", base / "first", base / "second"
    for directory, module in ((sysroot / "lib/lean", "Init"), (first, "Library"), (second, "Model")):
        directory.mkdir(parents=True)
        (directory / f"{module}.olean").write_bytes(b"")
    if conflict:
        (second / "Library.olean").write_bytes(b"")
    return sysroot, (first, second)


@pytest.fixture
def scans(monkeypatch: pytest.MonkeyPatch) -> list[Path]:
    """Count directory scans and start each test with no remembered roots."""
    monkeypatch.setattr(runtime, "VALIDATED_LIBRARY_ROOTS", set())
    scanned: list[Path] = []
    original = Path.rglob

    def counted(directory: Path, pattern: str) -> Iterator[Path]:
        """Record the scanned directory and run the real scan."""
        scanned.append(directory)
        return original(directory, pattern)

    monkeypatch.setattr(Path, "rglob", counted)
    return scanned


def test_second_check_of_the_same_roots_does_not_scan(tmp_path: Path, scans: list[Path]) -> None:
    """A second check of the same roots, also through a symbolic link, reads no directory."""
    sysroot, libraries = roots(tmp_path)
    validate_libraries(sysroot, libraries)
    assert len(scans) == 3
    (tmp_path / "link").symlink_to(libraries[0])
    validate_libraries(sysroot, (tmp_path / "link", libraries[1]))
    assert len(scans) == 3


def test_conflict_is_refused_on_every_check(tmp_path: Path, scans: list[Path]) -> None:
    """A refused set of roots is scanned and refused again, not remembered."""
    sysroot, libraries = roots(tmp_path, conflict=True)
    for _ in range(2):
        with pytest.raises(ValueError, match="conflicts with"):
            validate_libraries(sysroot, libraries)
    assert len(scans) == 6
    assert not runtime.VALIDATED_LIBRARY_ROOTS

