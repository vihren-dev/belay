"""Actual Lean server observations of table information in `INSERT ... SELECT` (editor task, part 3)."""

from pathlib import Path

import pytest

from tests.lean_server_support import LeanServer, diagnostics, position, semantic_tokens, table_hover
from tests.surface_editor_support import definitions, hover_text_or_none, range_of

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

SOURCE = '''import Belay
open Belay.Sqlite
def shop : Database := db! r"CREATE TABLE orders(id INTEGER PRIMARY KEY, label TEXT NOT NULL COLLATE NOCASE, qty INTEGER);
  CREATE TABLE archive(id INTEGER, label TEXT, qty INTEGER);
  CREATE TABLE tags(order_id INTEGER, tag TEXT);
  INSERT INTO orders VALUES (1, 'a', 5), (2, 'b', 6)"
def copies := sql! shop r"INSERT INTO archive SELECT id, label, qty FROM orders WHERE id IN (SELECT order_id FROM tags)
    AND qty > (SELECT max(o2.qty) FROM orders AS o2 JOIN tags AS t2 ON 1);
  INSERT INTO archive SELECT id, label, qty FROM orders JOIN tags AS t3 ON 1"
def shadowed := sql! shop r"WITH orders AS (SELECT 1, 'x', 2) INSERT INTO archive SELECT * FROM orders"
def shadowedInner := sql! shop r"WITH tags AS (SELECT 1) INSERT INTO archive SELECT id, label, qty FROM orders
    WHERE id IN (SELECT * FROM tags)"
def escaped := sql! shop "INSERT INTO archive SELECT id, label, qty FROM orders\\n"
def plain := sql r"INSERT INTO archive SELECT id, label, qty FROM orders AS plain_use"
def finished : Nat := 0
'''


def test_insert_select_table_hovers(runtime_root: Path, tmp_path: Path) -> None:
    """Our table places of `INSERT ... SELECT` (`SqlTableSlots.tableSlotsOf`) reach the real server:
    the target, the source, the sources of the subqueries (a `FROM` source and a join source) and
    the join of the next statement get the table hover with the rows known before the first write
    and none after it, each at its exact range, with the `property` token. A name that a `WITH` definition of
    the statement also names gets no information, in the query and in a subquery, and neither do
    plain `sql` and an escaped literal."""
    server = LeanServer(runtime_root, tmp_path, module="EditorFixture")
    try:
        uri = server.open(SOURCE)
        tokens = semantic_tokens(server, uri)
        target = table_hover(server, uri, SOURCE, "archive SELECT", 0, "archive")
        assert target.startswith("Table `archive` of `shop`.") and "0 rows at this point" in target, target
        for spelling, name, rows in (("orders WHERE", "orders", "2 rows"), ("tags)", "tags", "0 rows"),
                                     ("orders AS o2", "orders", "2 rows"), ("tags AS t2", "tags", "0 rows")):
            text = table_hover(server, uri, SOURCE, spelling, 0, name)
            assert text.startswith(f"Table `{name}` of `shop`.") and f"{rows} at this point" in text, text
            start = position(SOURCE, spelling, 0)
            assert (start["line"], start["character"], len(name), "property") in tokens, (spelling, tokens)
        for spelling, name in (("archive SELECT", "archive"), ("orders JOIN", "orders"), ("tags AS t3", "tags")):
            text = table_hover(server, uri, SOURCE, spelling, 1 if name == "archive" else 0, name)
            assert f"Table `{name}` of `shop`." in text and "at this point of the script" not in text, text
        for spelling in ("orders\\n\"", "orders AS plain_use", "orders AS (SELECT 1", "orders\"", "tags AS (SELECT 1)", "tags)\""):
            assert "Table `" not in hover_text_or_none(server, uri, SOURCE, spelling, 0), spelling
        assert "Table `orders`" in hover_text_or_none(server, uri, SOURCE, "orders\n    WHERE id IN (SELECT *", 0)
        assert not [item for item in diagnostics(server, uri) if item["severity"] == 1]
    finally:
        server.close()


def test_insert_select_navigation(runtime_root: Path, tmp_path: Path) -> None:
    """Our table origins (`SqlTableOrigins`) reach the sources of `INSERT ... SELECT`: the target, the
    source, and the sources of its subqueries navigate to their `CREATE TABLE` in the database text,
    and a name that a `WITH` definition names has no target."""
    server = LeanServer(runtime_root, tmp_path, module="EditorFixture")
    try:
        uri = server.open(SOURCE)
        for spelling, occurrence, created in (("archive SELECT", 0, "archive(id"), ("orders WHERE", 0, "orders(id"),
                                              ("tags)", 0, "tags(order_id"), ("tags AS t2", 0, "tags(order_id"),
                                              ("orders AS o2", 0, "orders(id")):
            name = created.split("(")[0]
            assert definitions(server, uri, SOURCE, spelling, occurrence) == [
                (uri, range_of(SOURCE, created, name))], spelling
        assert definitions(server, uri, SOURCE, "orders AS (SELECT 1") == []
        assert definitions(server, uri, SOURCE, "tags AS (SELECT 1)") == []
        assert definitions(server, uri, SOURCE, "orders\"") == []
    finally:
        server.close()
