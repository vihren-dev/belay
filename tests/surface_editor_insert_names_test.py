"""Actual Lean server observations of the names of `INSERT ... SELECT` (editor task, part 3)."""

from pathlib import Path

import pytest

from tests.lean_server_support import LeanServer, diagnostics, position, semantic_tokens
from tests.surface_editor_support import corrections, name_hover

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

SOURCE = '''import Belay
open Belay.Sqlite
def shop : Database := db! r"CREATE TABLE orders(id INTEGER PRIMARY KEY, label TEXT NOT NULL COLLATE NOCASE, qty INTEGER, price REAL);
  CREATE TABLE archive(id INTEGER, label TEXT, qty INTEGER)"
def good := sql! shop r"INSERT INTO archive(id, label, qty) SELECT o.id, label, qty FROM orders AS o WHERE qty = 1"
def valuesForm := sql! shop r"INSERT INTO archive(id, label, qty) VALUES (1, 'a', 2)"
def withDefinition := sql! shop r"WITH orders AS (SELECT 1 AS id, 'x' AS label, 2 AS qty)
  INSERT INTO archive SELECT id, label, qty FROM orders WHERE qty = 2"
def finished : Nat := 0
'''

TYPOS = '''import Belay
open Belay.Sqlite
def shop : Database := db! r"CREATE TABLE orders(id INTEGER PRIMARY KEY, label TEXT NOT NULL COLLATE NOCASE, qty INTEGER, price REAL);
  CREATE TABLE archive(id INTEGER, label TEXT, qty INTEGER)"
def typoQuery := sql! shop r"INSERT INTO archive SELECT id, lable, qty FROM orders"
def typoTarget := sql! shop r"INSERT INTO archive(id, lable, qty) SELECT id, label, qty FROM orders"
def typoTable := sql! shop r"INSERT INTO archve SELECT id, label, qty FROM orders"
def typoSource := sql! shop r"INSERT INTO archive SELECT id, label, qty FROM ordrs"
def typoSubquery := sql! shop r"INSERT INTO archive SELECT id, label, qty FROM orders WHERE id IN (SELECT lable FROM orders)"
def distant := sql! shop r"INSERT INTO archive SELECT id, far_away_name, qty FROM orders"
def literal := sql! shop r##"INSERT INTO archive SELECT id, "labl", qty FROM orders"##
def quotedColumn := sql! shop r##"INSERT INTO archive SELECT id, "label", qty FROM orders"##
def ambiguous := sql! shop r"INSERT INTO archive SELECT id, label, qty FROM orders, orders AS again"
def finished : Nat := 0
'''


def test_insert_select_column_information(runtime_root: Path, tmp_path: Path) -> None:
    """Our column information (`SqlNameInfo`, from the name trace of `resolveInsertQueryTraced`) reaches the
    real server for `INSERT ... SELECT`: the target column list has the same hover as the list of
    `INSERT ... VALUES`, the names of the query show their table, alias, declared type, affinity and
    collation, the comparison of the `WHERE` clause shows its affinity, and the columns of a `WITH`
    definition of the statement are derived columns."""
    server = LeanServer(runtime_root, tmp_path)
    try:
        uri = server.open(SOURCE)
        for spelling, token, rest in (("id, label, qty) SELECT", "id", "INTEGER"), ("label, qty) SELECT", "label", "TEXT"),
                                      ("qty) SELECT", "qty", "INTEGER")):
            select = name_hover(server, uri, SOURCE, spelling, 0, token)
            values = name_hover(server, uri, SOURCE, spelling.replace("SELECT", "VALUES"), 0, token)
            assert select == values and select.startswith(f"Column `{token}` of table `archive`."), (select, values)
            assert f"Declared type: {rest}." in select, select
        label = name_hover(server, uri, SOURCE, "label, qty FROM", 0, "label")
        assert label.startswith("Column `label` of table `orders` (alias `o`).") and "Collation: NOCASE." in label, label
        qty = name_hover(server, uri, SOURCE, "qty = 1", 0, "qty")
        assert "Column `qty` of table `orders` (alias `o`)." in qty and "Declared type: INTEGER." in qty, qty
        derived = name_hover(server, uri, SOURCE, "qty FROM orders WHERE qty = 2", 0, "qty")
        assert derived.startswith("Column `qty` of WITH definition `orders`.") and "Derived column" in derived, derived
        tokens = semantic_tokens(server, uri)
        start = position(SOURCE, "label, qty FROM")
        assert (start["line"], start["character"], 5, "variable") in tokens, tokens
        assert not [item for item in diagnostics(server, uri) if item["severity"] == 1]
    finally:
        server.close()


def test_insert_select_corrections_and_literal_warning(runtime_root: Path, tmp_path: Path) -> None:
    """Our corrections and DQS warning (`SqlNameCorrections`, `SqlNameInfo`) reach the real server for the
    names of `INSERT ... SELECT`: a unique typo in the query, in the target column list, in a subquery, in the
    target table and in the source table gets one quick fix at the written name, a distant name gets none, an
    unknown double-quoted name of the query is a warning that reads it as a text literal with the quoted fix,
    a quoted existing column gets no warning, and an ambiguous name gets no fix."""
    server = LeanServer(runtime_root, tmp_path)
    try:
        uri = server.open(TYPOS)
        for spelling, token, fixed in (("lable, qty FROM", "lable", "label"), ("lable, qty) SELECT", "lable", "label"),
                                       ("lable FROM orders)", "lable", "label"), ("archve", "archve", "archive"),
                                       ("ordrs", "ordrs", "orders")):
            assert corrections(server, uri, TYPOS, spelling, 0, token) == [(f"Replace {token} with {fixed}", fixed)], spelling
        assert corrections(server, uri, TYPOS, "far_away_name", 0, "far_away_name") == []
        assert corrections(server, uri, TYPOS, '"labl"', 0, '"labl"') == [('Replace "labl" with "label"', '"label"')]
        assert corrections(server, uri, TYPOS, "id, label, qty FROM orders, ", 0, "id") == []
        found = diagnostics(server, uri)
        warnings = [item for item in found if item["severity"] == 2]
        assert len(warnings) == 1 and "text literal 'labl'" in warnings[0]["message"], warnings
        line = position(TYPOS, "def literal")["line"]
        assert warnings[0]["range"]["start"]["line"] == line, warnings
        errors = [item["message"] for item in found if item["severity"] == 1]
        assert len(errors) == 7 and any("ambiguous column name: id" in message for message in errors), errors
    finally:
        server.close()
