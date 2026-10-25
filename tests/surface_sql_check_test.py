"""S7 freshness checker: `belay-sql-check` compares compiled SQL-file records with the files, without rebuilding."""

import json
import os
from pathlib import Path
import shutil

import pytest

from tests.runtime_support import CommandResult
from tests.sql_file_support import installed_layout, lake_build, run_checker, write_lean_package, write_package

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

USES_A = 'import Belay\n\n/-- The first use of `sql/a.sql`. -/\ndef first := sql_file "sql/a.sql"\n/-- A second use. -/\ndef second := sql_file "sql/a.sql"\n'
"""A library module with two declarations that read one file."""
USES_AB = 'import Belay\n\n/-- Reads both files. -/\ndef both := sql_file "sql/a.sql"\n/-- Reads the other file. -/\ndef other := sql_file "sql/b.sql"\n'
"""A library module that reads two files, one of them shared with the other library."""
NO_SQL = 'import Belay\n\n/-- A module that reads no SQL file. -/\ndef plain := sql "SELECT 1"\n'
"""A library module that has no SQL records."""


def make_consumer(runtime_root: Path, tmp_path: Path) -> tuple[Path, Path]:
    """A package with the libraries Alpha (one file, two uses), Beta (two files) and Plain (no SQL)."""
    installed = installed_layout(runtime_root, tmp_path)
    package = tmp_path / "consumer"
    write_lean_package(package, "Checked", installed, ["Alpha", "Beta", "Plain"])
    (package / "sql/a.sql").write_bytes(b"SELECT 1;\r\nSELECT 2;\r\n")
    (package / "sql/b.sql").write_text("SELECT 3;\n")
    for library, text in {"Alpha": USES_A, "Beta": USES_AB, "Plain": NO_SQL}.items():
        (package / f"lean/{library}.lean").write_text(text)
    return installed, package


def build_all(installed: Path, package: Path) -> None:
    """Build the three libraries once."""
    for library in ("Alpha", "Beta", "Plain"):
        result = lake_build(installed, package, library)
        assert result.returncode == 0, result.diagnostic()


def modification_times(package: Path) -> dict[str, int]:
    """The modification time of every compiled Lean artifact, to show that a check builds nothing."""
    return {str(path): path.stat().st_mtime_ns for path in (package / ".lake/build").rglob("*") if path.is_file()}


def lines(result: CommandResult) -> list[str]:
    """The report lines on standard output."""
    return result.stdout.splitlines()


def test_totals_by_library_and_the_selector(runtime_root: Path, tmp_path: Path) -> None:
    """`checkLibrary` and `selectLibraries` (`BelaySqlCheck.lean`) report each library's distinct sources: two uses of
    one file count once, a library without SQL reports zero, and `--library` selects one library or refuses an
    unknown name."""
    installed, package = make_consumer(runtime_root, tmp_path)
    build_all(installed, package)
    result = run_checker(installed, package)
    assert result.returncode == 0, result.diagnostic()
    assert lines(result) == ["library Alpha: 1 modules, 1 SQL sources, 0 stale",
                             "library Beta: 1 modules, 2 SQL sources, 0 stale",
                             "library Plain: 1 modules, 0 SQL sources, 0 stale"], result.diagnostic()
    selected = run_checker(installed, package, "--library", "Beta")
    assert selected.returncode == 0 and lines(selected) == ["library Beta: 1 modules, 2 SQL sources, 0 stale"]
    unknown = run_checker(installed, package, "--library", "Missing")
    assert unknown.returncode == 2 and "the package has no library Missing" in unknown.stderr, unknown.diagnostic()


def test_a_stale_source_is_reported_before_any_rebuild(runtime_root: Path, tmp_path: Path) -> None:
    """`checkSource` (`BelaySqlCheck.lean`) and `LibraryCheck.render` (`SqlCheckReport.lean`): an SQL edit without a
    Lean edit gives a nonzero result that names the package, path, declarations and the rebuild command; the check
    changes no artifact; a line-ending-only edit stays fresh; a rebuild restores success."""
    installed, package = make_consumer(runtime_root, tmp_path)
    build_all(installed, package)
    before = modification_times(package)
    (package / "sql/a.sql").write_bytes(b"SELECT 1;\nSELECT 2;\n")
    assert run_checker(installed, package).returncode == 0
    (package / "sql/a.sql").write_bytes(b"SELECT 1;\nSELECT 9;\n")
    result = run_checker(installed, package)
    assert result.returncode == 1, result.diagnostic()
    assert "library Alpha: 1 modules, 1 SQL sources, 1 stale" in lines(result)
    assert "  Checked: sql/a.sql changed since the library was built (used by first, second); rebuild with: lake build Alpha" in lines(result)
    assert any(line.startswith("  Checked: sql/a.sql changed") and "rebuild with: lake build Beta" in line for line in lines(result))
    assert modification_times(package) == before, "the checker rebuilt a library"
    shutil.rmtree(package / ".lake/build")
    build_all(installed, package)
    assert run_checker(installed, package).returncode == 0


def test_missing_files_and_missing_compiled_modules(runtime_root: Path, tmp_path: Path) -> None:
    """`sourceState` and `walkModule` (`SqlCheckReport.lean`, `BelaySqlCheck.lean`): a deleted SQL file is a stale
    source; a library whose compiled module is gone or damaged is an explicit error with the build command, and not a
    report of zero sources."""
    installed, package = make_consumer(runtime_root, tmp_path)
    build_all(installed, package)
    (package / "sql/b.sql").unlink()
    result = run_checker(installed, package, "--library", "Beta")
    assert result.returncode == 1 and "sql/b.sql is missing (used by other)" in result.stdout, result.diagnostic()
    for artifact in (package / ".lake/build/lib/lean").glob("Alpha.*"):
        artifact.unlink()
    result = run_checker(installed, package, "--library", "Alpha")
    assert result.returncode == 2 and "library Alpha: module Alpha has no compiled file" in result.stderr and "run lake build Alpha to compile it" in result.stderr, result.diagnostic()
    (package / ".lake/build/lib/lean/Beta.olean").write_bytes(b"not a compiled module")
    result = run_checker(installed, package, "--library", "Beta")
    assert result.returncode == 2 and "library Beta: cannot read the compiled module Beta" in result.stderr and "run lake build Beta" in result.stderr, result.diagnostic()


def test_dependency_records_are_checked_against_the_dependency_files(runtime_root: Path, tmp_path: Path) -> None:
    """`walkModule` and `packagesNamed` (`BelaySqlCheck.lean`): records reached through an import map to the
    dependency package's own files, also after the whole tree moved, and an edit there is stale in the library that
    imports it."""
    installed = installed_layout(runtime_root, tmp_path)
    dependency = tmp_path / "dependency"
    write_package(dependency, "SqlDependency", installed)
    (dependency / "sql/dep.sql").write_text("SELECT 7;\n")
    (dependency / "lean/SqlDependency.lean").write_text(
        'import Belay\n\n/-- Reads the dependency file. -/\ndef fromDependency := sql_file "sql/dep.sql"\n')
    consumer = tmp_path / "consumer"
    write_lean_package(consumer, "Importer", installed, ["Importer"],
                       inputs=f'require SqlDependency from {json.dumps("../dependency")}')
    (consumer / "lean/Importer.lean").write_text('import SqlDependency\n')
    result = lake_build(installed, consumer, "Importer")
    assert result.returncode == 0, result.diagnostic()
    result = run_checker(installed, consumer)
    assert result.returncode == 0 and lines(result) == ["library Importer: 1 modules, 1 SQL sources, 0 stale"], result.diagnostic()
    moved = tmp_path / "moved"
    moved.mkdir()
    shutil.copytree(dependency, moved / "dependency", symlinks=True)
    shutil.copytree(consumer, moved / "consumer", symlinks=True)
    result = run_checker(installed, moved / "consumer")
    assert result.returncode == 0, result.diagnostic()
    (moved / "dependency/sql/dep.sql").write_text("SELECT 8;\n")
    result = run_checker(installed, moved / "consumer")
    assert result.returncode == 1 and "SqlDependency: sql/dep.sql changed" in result.stdout, result.diagnostic()
    assert run_checker(installed, consumer).returncode == 0, "the original tree still has the file that it was built from"
