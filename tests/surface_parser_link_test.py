"""The Lake output of the text package and the surface holds the parser (ADR 0023, D5).

The runtime root of the `surface` suite has the programs and shared libraries that Lake built
(`build-support/tests.nix`, `surfaceRoot`). These tests check our link configuration in
`packages/belay-sqlite-text/lakefile.lean` and our C library declarations in `parser/c-headers`.
"""

from pathlib import Path

import pytest

from tests.parser_object_symbols import DARWIN, run_tool, undeclared_calls

pytestmark = [pytest.mark.integration, pytest.mark.parser]
LIBRARY_PATTERN = "lib*.dylib" if DARWIN else "lib*.so"
"""The shared libraries of a package, by file name."""


def dependencies(path: Path) -> str:
    """The dependencies of a file. `otool -L` also prints the file name and, for a library, its own
    install name, so on macOS these lines are left out."""
    if not DARWIN:
        return run_tool("ldd", str(path))
    lines = run_tool("otool", "-L", str(path)).splitlines()[1:]
    return "\n".join(line for line in lines if Path(line.split()[0]).name != path.name)


def program_files(runtime_root: Path) -> list[Path]:
    """Each program and shared library of the text package and the surface that contains the parser."""
    text, surface = (runtime_root / f"packages/{name}/.lake/build" for name in ("belay-sqlite-text", "belay"))
    programs = [text / "bin/belay-sqlite-translate", surface / "bin/belay-sql-check"]
    libraries = sorted((text / "lib").glob(LIBRARY_PATTERN)) + sorted((surface / "lib").glob(LIBRARY_PATTERN))
    return programs + libraries


def test_no_program_or_library_depends_on_a_parser_library(runtime_root: Path) -> None:
    """`ldd` (Linux) or `otool -L` (macOS) of the translation program, the SQL-file checker and the
    shared libraries of the text package and the surface lists no parser library: Lake links the
    parser's C into them, so a loader needs nothing outside the toolchain and the C library."""
    files = program_files(runtime_root)
    assert len(files) > 4, files
    for path in files:
        assert path.is_file(), f"{path} is missing; add a program or shared library of the parser to this list"
        listing = dependencies(path)
        assert "parser" not in listing.lower(), f"{path} depends on a parser library:\n{listing}"


def test_objects_call_only_the_declared_c_library_functions(runtime_root: Path) -> None:
    """The undefined symbols of each object that the text package compiles from the C of `parser`
    are defined by another object of the library, or are one of `DECLARED_C_FUNCTIONS` of `tests/parser_object_symbols.py`. The headers of
    `parser/c-headers` declare only what the units use, so a new C library function needs a new entry."""
    objects = sorted((runtime_root / "packages/belay-sqlite-text/.lake/build/c/parser").glob("*.o"))
    assert len(objects) >= 3, objects
    calls = undeclared_calls(objects)
    assert not calls, f"review the declarations of these calls in parser/c-headers: {calls}"
