"""The C library functions that the parser's objects may call (ADR 0023, D5).

The text package's lakefile compiles the C of `parser` with the declarations of
`parser/c-headers`. A wrong declaration compiles and links without an error, so the objects may
call only the functions whose declarations were reviewed. The Nix link test
(`tests/surface_parser_link_test.py`) checks the objects of the Nix build, and the local-loop
test (`tests/dev_loop_test.py`) checks those of `just dev-build`.
"""

from pathlib import Path
import subprocess
import sys

DARWIN = sys.platform == "darwin"
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


def symbols(path: Path, *options: str) -> set[str]:
    """The symbols of an object that `nm` lists with the options, without the leading underscore of macOS."""
    names = {line.split()[-1] for line in run_tool("nm", *options, str(path)).splitlines() if line.strip()}
    return {name[1:] if DARWIN and name.startswith("_") else name for name in names}


def undeclared_calls(objects: list[Path]) -> dict[str, list[str]]:
    """For each object, the undefined symbols that no other object of `objects` defines and that are
    not in `DECLARED_C_FUNCTIONS`. Objects with no such symbol are left out."""
    defined_options = ("-gU",) if DARWIN else ("-g", "--defined-only")
    defined = {path: symbols(path, *defined_options) for path in objects}
    calls: dict[str, list[str]] = {}
    for path in objects:
        others = set().union(*(names for other, names in defined.items() if other != path))
        undefined = symbols(path, "-u") - others - set(DECLARED_C_FUNCTIONS)
        if undefined:
            calls[path.name] = sorted(undefined)
    return calls
