"""Actual Lean server observations of table information in `sql!` text (editor task, part 2a)."""

from pathlib import Path

import pytest

from tests.lean_server_support import LeanServer, hover, position, semantic_tokens

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

SOURCE = '''import Belay
open Belay.Sqlite
def shop : Database := db! r"CREATE TABLE orders(id INTEGER PRIMARY KEY, label TEXT NOT NULL COLLATE NOCASE);
  INSERT INTO orders VALUES (1, 'a'), (2, 'b')"
def reads := sql! shop r##"SELECT '😀' FROM orders;
  SELECT * FROM "orders" AS o JOIN orders ON 1;
  INSERT INTO orders VALUES (3, 'c');
  SELECT * FROM orders; DELETE FROM orders"##
def schema := sql! shop r"CREATE TABLE extra(x); SELECT * FROM extra; DROP TABLE extra"
def viewed : Database := db! r"CREATE VIEW v AS SELECT 1; CREATE TABLE stock(n); INSERT INTO stock VALUES (1)"
def views := sql! viewed r"SELECT * FROM stock; DROP VIEW v; SELECT * FROM stock"
def shadowed := sql! shop r"WITH orders AS (SELECT 1) SELECT * FROM orders AS shade"
def plain := sql r"SELECT * FROM orders WHERE 1"
def escaped := sql! shop "SELECT * FROM orders; SELECT 'a\\nb'"
def finished : Nat := 0
'''


def table_hover(server: LeanServer, uri: str, source: str, spelling: str, occurrence: int,
                token: str) -> str:
    """The hover text of one table occurrence; the hover range must be exactly the written token."""
    start = position(source, spelling, occurrence)
    result = hover(server, uri, start)
    contents = result["contents"]
    assert isinstance(contents, dict) and isinstance(contents["value"], str), result
    end = {**start, "character": start["character"] + len(token)}
    assert result["range"] == {"start": start, "end": end}, result
    return contents["value"]


def no_table_information(server: LeanServer, uri: str, source: str, spelling: str, occurrence: int,
                         tokens: list[tuple[int, int, int, str]]) -> None:
    """The occurrence has no hover with table facts and no extra semantic token."""
    start = position(source, spelling, occurrence)
    result = server.request("textDocument/hover", {"textDocument": {"uri": uri}, "position": start})
    assert "Table `" not in str(result), result
    assert not any(line == start["line"] and column == start["character"]
                   for line, column, _, _ in tokens), tokens


@pytest.mark.parametrize("newline", ["\n", "\r\n"], ids=["lf", "crlf"])
def test_sql_bang_table_hovers(runtime_root: Path, tmp_path: Path, newline: str) -> None:
    """Our table information (`SqlEditorInfo`) reaches the real server: catalog facts, row counts that
    stop at the first write, sequential schema changes, quoted names, CTE shadowing, and exact UTF-16
    ranges after non-BMP text. Plain `sql` and an escaped literal get no table information."""
    source = SOURCE.replace("\n", newline)
    server = LeanServer(runtime_root, tmp_path)
    try:
        uri = server.open(source)
        tokens = semantic_tokens(server, uri)
        first = table_hover(server, uri, source, "orders;", 0, "orders")
        assert first.startswith("Table `orders` of `shop`."), first
        assert "`id`: INTEGER, PRIMARY KEY" in first, first
        assert "`label`: TEXT, NOT NULL, COLLATE NOCASE" in first, first
        assert "2 rows at this point of the script." in first, first
        where = position(source, "orders;", 0)
        assert (where["line"], where["character"], 6, "property") in tokens, tokens
        for spelling, token in (('"orders"', '"orders"'), ("orders ON", "orders"), ("orders VALUES (3", "orders")):
            assert "2 rows at this point" in table_hover(server, uri, source, spelling, 0, token), spelling
        for spelling in ("orders; DELETE", 'orders"##'):
            text = table_hover(server, uri, source, spelling, 0, "orders")
            assert "at this point of the script" not in text and "`id`: INTEGER" in text, text
        created = table_hover(server, uri, source, "extra;", 0, "extra")
        assert "`x`: no declared type" in created and "at this point of the script" not in created, created
        assert "`x`: no declared type" in table_hover(server, uri, source, 'extra"', 0, "extra")
        assert "1 row at this point of the script." in table_hover(server, uri, source, "stock;", 0, "stock")
        dropped = table_hover(server, uri, source, "stock\"", 0, "stock")
        assert "`n`: no declared type" in dropped and "at this point of the script" not in dropped, dropped
        for spelling in ("orders AS (SELECT", "orders AS shade", "orders WHERE 1", "orders; SELECT 'a"):
            no_table_information(server, uri, source, spelling, 0, tokens)
        diagnostics = [message for message in server.notifications
                       if message.get("method") == "textDocument/publishDiagnostics"]
        for message in diagnostics:
            params = message["params"]
            assert isinstance(params, dict) and not params["diagnostics"], message
    finally:
        server.close()
