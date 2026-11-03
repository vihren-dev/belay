"""The Lake output of the text package and the surface holds the parser (ADR 0023, D5).

The runtime root of the `surface` suite has the programs and shared libraries that Lake built
(`build-support/tests.nix`, `surfaceRoot`). These tests check our link configuration in
`packages/belay-sqlite-text/lakefile.lean` and our C library declarations in `parser/c-headers`.
"""

from pathlib import Path
import subprocess
import sys

import pytest

pytestmark = [pytest.mark.integration, pytest.mark.parser]
DARWIN = sys.platform == "darwin"
LIBRARY_PATTERN = "lib*.dylib" if DARWIN else "lib*.so"
"""The shared libraries of a package, by file name."""
TOOL_SECONDS = 60
"""The limit for one run of `ldd`, `otool` or `nm`."""
DECLARED_C_FUNCTIONS: dict[str, str] = {
    # Each function is declared in parser/c-headers with its standard C signature, which the linker
    # resolves in the C library that Lean links. A wrong declaration compiles and links without an error.
    "calloc": "stdlib.h: void *calloc(size_t, size_t). Allocates the arrays of the library's API.",
    "free": "stdlib.h: void free(void *). Releases the documents, the parser and the syntax tree.",
    "malloc": "stdlib.h: void *malloc(size_t). Allocates the parser, which Lemon takes as a function pointer.",
    "realloc": "stdlib.h: void *realloc(void *, size_t). Grows the document and the syntax tree.",
    "fprintf": "stdio.h: int fprintf(FILE *, const char *, ...). Lemon's trace output; FILE is used "
               "only through a pointer, so it stays incomplete.",
    "fwrite": "stdio.h: size_t fwrite(const void *, size_t, size_t, FILE *). Lemon's trace output.",
    "snprintf": "stdio.h: int snprintf(char *, size_t, const char *, ...). Writes the decimal numbers "
                "of a document.",
    "memcpy": "string.h: void *memcpy(void *, const void *, size_t). Copies children and text.",
    "strcmp": "string.h: int strcmp(const char *, const char *). Compares grammar identities.",
    "strlen": "string.h: size_t strlen(const char *). Measures the NUL-terminated texts of a document.",
}
"""The C library functions that the objects compiled from the C of `parser/generated` may call and no
other object of the library defines: the ten functions of ADR 0023, fact 6. A new function here
needs a review of its declaration in `parser/c-headers`."""


def run_tool(*command: str) -> str:
    """The standard output of a tool that must succeed, with a finite timeout."""
    result = subprocess.run(command, capture_output=True, text=True, timeout=TOOL_SECONDS, check=False)
    assert result.returncode == 0, f"{' '.join(command)}: {result.stderr}"
    return result.stdout


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


def symbols(path: Path, *options: str) -> set[str]:
    """The symbols of an object that `nm` lists with the options, without the leading underscore of macOS."""
    names = {line.split()[-1] for line in run_tool("nm", *options, str(path)).splitlines() if line.strip()}
    return {name[1:] if DARWIN and name.startswith("_") else name for name in names}


def test_objects_call_only_the_declared_c_library_functions(runtime_root: Path) -> None:
    """The undefined symbols of each object that the text package compiles from the C of `parser`
    are defined by another object of the library, or are one of `DECLARED_C_FUNCTIONS`. The headers of
    `parser/c-headers` declare only what the units use, so a new C library function needs a new entry."""
    objects = sorted((runtime_root / "packages/belay-sqlite-text/.lake/build/c/parser").glob("*.o"))
    assert len(objects) >= 3, objects
    defined_options = ("-gU",) if DARWIN else ("-g", "--defined-only")
    defined = {path: symbols(path, *defined_options) for path in objects}
    for path in objects:
        others = set().union(*(names for other, names in defined.items() if other != path))
        undefined = symbols(path, "-u") - others - set(DECLARED_C_FUNCTIONS)
        assert not undefined, f"{path.name} calls {sorted(undefined)}; review their declarations in parser/c-headers"
