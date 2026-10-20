"""The function catalog of the model matches the pinned library (ADR 0015, D1).

`Belay/Sqlite/Resolution/FunctionCatalog.lean` lists each function name with the numbers of
arguments that its scalar, aggregate or window form accepts. Resolution reports SQLite's
`no such function` and `wrong number of arguments` from it, so a name or a number that
differs from the library would give a wrong prepare error. The test reads the Lean table and
compares it with `PRAGMA function_list` of a connection of the pinned library, with native
SQLite as the oracle.
"""

import re
import tempfile
from pathlib import Path

import pytest

from conformance.native_connection import Connection, library_path
from conformance.native_library import load_library

pytestmark = [pytest.mark.integration, pytest.mark.requires_native("sqlite3")]
CATALOG = Path(__file__).resolve().parents[1] / "packages/belay-sqlite/Belay/Sqlite/Resolution/FunctionCatalog.lean"
ENTRY = re.compile(r'^  \| "(?P<name>[^"]+)" => some \{ (?P<forms>[^}]*) \}$', re.MULTILINE)
FORM = re.compile(r"(?P<kind>scalar|aggregate|window) := some \(\.(?P<arity>counts \[[^]]*\]|atLeast \d+)\)")
WINDOW_ONLY = {"cume_dist", "dense_rank", "first_value", "lag", "last_value", "lead", "nth_value", "ntile",
               "percent_rank", "rank", "row_number"}
"""The functions of the library that run only as window functions."""


def lean_catalog() -> dict[str, dict[str, str]]:
    """The arity of each form of each function in the Lean table, as written in Lean."""
    return {match["name"]: {form["kind"]: form["arity"] for form in FORM.finditer(match["forms"])}
            for match in ENTRY.finditer(CATALOG.read_text())}


def arity(counts: set[int]) -> str:
    """The Lean arity of the `narg` values of one form: -1 is any number, -N for N of 2 or
    more is at least N - 2, and other values are exact counts."""
    negative = [count for count in counts if count < 0]
    if negative:
        assert len(counts) == 1, counts
        return f"atLeast {0 if negative[0] == -1 else -negative[0] - 2}"
    return "counts [" + ", ".join(str(count) for count in sorted(counts)) + "]"


def native_catalog() -> dict[str, dict[str, str]]:
    """The arity of each form of each function of `PRAGMA function_list`, built-in or not."""
    with tempfile.TemporaryDirectory() as directory:
        connection = Connection(load_library(library_path()), Path(directory) / "catalog.db")
        rows = connection.query("SELECT name, type, narg FROM pragma_function_list")
        connection.close()
    forms: dict[str, dict[str, set[int]]] = {}
    for (_, name), (_, kind), (_, count) in rows:
        text = name.decode()
        key = "scalar" if kind == b"s" else "window" if text in WINDOW_ONLY else "aggregate"
        forms.setdefault(text, {}).setdefault(key, set()).add(count)
    return {name: {key: arity(counts) for key, counts in kinds.items()} for name, kinds in forms.items()}


def test_lean_catalog_matches_the_library() -> None:
    """Each name of the library is in the Lean table with the same arities, and the table has
    no other name: 141 built-in names and `match`."""
    lean, native = lean_catalog(), native_catalog()
    assert len(lean) == 142
    assert lean == native
