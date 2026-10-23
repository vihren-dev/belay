"""Keep default resolution aligned with pinned SQLite preparation boundaries."""

import ctypes as c
from pathlib import Path

import pytest

from conformance.native_connection import Connection, library_path
from conformance.native_library import library_binary, load_library
from tests.shared_table_shape_test import compile_checks

pytestmark = [pytest.mark.integration, pytest.mark.kernel,
              pytest.mark.requires_lean("compiler"),
              pytest.mark.requires_native("sqlite3", "sqlite3-3.46.0")]

CASES = [
    ("(1=1)", '.compare .eq (.numeric "1") (.numeric "1")'),
    ("(NULL=1)", '.compare .eq .null (.numeric "1")'),
    ("(CURRENT_TIMESTAMP=CURRENT_TIMESTAMP)",
     '.compare .eq (.currentTime "CURRENT_TIMESTAMP") (.currentTime "CURRENT_TIMESTAMP")'),
    ("(foo=foo)", '.compare .eq (.identifier (name! "foo") .none) (.identifier (name! "foo") .none)'),
    ('("foo"="foo")', '.compare .eq (.identifier (name! "foo") .double) (.identifier (name! "foo") .double)'),
    ("foo", '.identifier (name! "foo") .none'),
    ("(+foo)", '.positive (.identifier (name! "foo") .none)'),
    ("(+true)", '.positive (.identifier (name! "true") .none)'),
    ("(-FaLsE)", '.negate (.identifier (name! "FaLsE") .none)'),
    ("(TRUE=1)", '.compare .eq (.identifier (name! "TRUE") .none) (.numeric "1")'),
    ('(+"true")', '.positive (.identifier (name! "true") .double)'),
    ('("false"=0)', '.compare .eq (.identifier (name! "false") .double) (.numeric "0")'),
    ("(-CURRENT_TIMESTAMP)", '.negate (.currentTime "CURRENT_TIMESTAMP")'),
]
"""Handwritten syntax pairs isolate our resolver from the frontend mapping."""


def native_prepares(version: str, sql: str, directory: Path) -> bool:
    """Whether the pinned SQLite of the version prepares ADD COLUMN with the default."""
    connection = Connection(load_library(library_path(library_binary(version)), version),
                            directory / "native.db")
    statement, tail = c.c_void_p(), c.c_char_p()
    try:
        connection.execute_script("CREATE TABLE IF NOT EXISTS t(id BLOB);")
        source = f"ALTER TABLE t ADD added BLOB DEFAULT {sql};".encode()
        code = connection.library.sqlite3_prepare_v2(connection.handle, source,
            len(source), c.byref(statement), c.byref(tail))
        assert code in (0, 1), connection.library.sqlite3_errmsg(connection.handle)
        return code == 0
    finally:
        if statement.value:
            connection.library.sqlite3_finalize(statement)
        connection.close()


@pytest.mark.parametrize("version", ["3.51.0", "3.46.0"])
def test_default_preparation_boundary(version: str, tmp_path: Path, lean_sysroot: Path,
        lean_libraries: tuple[Path, Path]) -> None:
    """Our constant predicate and ADD resolver preserve native preparation success, for each
    case of `CASES`; one Lean program checks all of them.

    Unmodeled defaults may produce a supported-domain refusal; modeled defaults
    resolve successfully. Neither may invent a preparation error.
    """
    prepares = [native_prepares(version, sql, tmp_path) for sql, _ in CASES]
    checks = "".join(f'''example : constantDefault ({expression}) = {str(prepared).lower()} := by decide +kernel
#eval ((resolveAddColumn {{ profile := Profile.documented "{version}" "", mode := .execution }}
    catalog 0 (name! "t") {{ name := name! "added", declaredType := some "BLOB", constraints := [.default ({expression}) "unused in preparation classification"] }}).toOption.map
  (fun pair => pair.1 == .prepareError (.expression (.defaultNotConstant (name! "added"))))).getD false
''' for (_, expression), prepared in zip(CASES, prepares, strict=True))
    source = f'''import Belay.Sqlite.Model.Resolution.AddColumn
open Belay.Sqlite.Model
def catalog : Catalog := [{{ name := name! "t", entry := .table {{
  columns := [{{name := name! "id", declaredType := some "BLOB"}}] }} }}]
{checks}'''
    lines = compile_checks(source, tmp_path, lean_sysroot, lean_libraries).split()
    assert lines == ["false" if prepared else "true" for prepared in prepares], list(zip(CASES, lines))
