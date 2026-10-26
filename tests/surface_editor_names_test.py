"""Actual Lean server observations of column and comparison information in `sql!` text (editor task, part 2b)."""

from pathlib import Path

import pytest

from tests.lean_server_support import LeanServer, diagnostics, position, semantic_tokens
from tests.surface_editor_support import hover_text_or_none, name_hover

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

SOURCE = '''import Belay
open Belay.Sqlite
def shop : Database := db! r"CREATE TABLE orders(id INTEGER PRIMARY KEY, label TEXT NOT NULL COLLATE NOCASE, qty INTEGER, price REAL);
  CREATE TABLE lines(order_id INTEGER REFERENCES orders(id), note TEXT UNIQUE);
  CREATE VIEW totals AS SELECT id AS key, qty + 1 AS next, label FROM orders"
def columns := sql! shop r"SELECT o.label, qty FROM orders AS o WHERE +qty = 1 AND CAST(qty AS TEXT) = 'x' AND qty IN (1, 2)"
def between := sql! shop r"SELECT 1 FROM orders WHERE qty BETWEEN 1 AND price"
def derived := sql! shop r"WITH w AS (SELECT qty FROM orders WHERE qty = 1) SELECT qty FROM w UNION ALL SELECT qty FROM w"
def subquery := sql! shop r"SELECT s.qty FROM (SELECT qty FROM orders) AS s; SELECT label FROM totals"
def foreign := sql! shop r"SELECT order_id, note FROM lines"
def shadow := sql! shop r"SELECT (SELECT qty FROM orders WHERE id = o.id) FROM orders AS o JOIN lines ON id = order_id"
def ambiguous := sql! shop r"SELECT id FROM orders, orders AS again"
def sequence := sql! shop r"CREATE TABLE t(x INTEGER); SELECT x FROM t; DROP TABLE t; CREATE TABLE t(x TEXT); SELECT x FROM t"
def viewed := sql! shop r"SELECT next, key FROM totals"
def plain := sql r"SELECT qty FROM orders"
example : (sql! shop r"SELECT qty FROM orders") = sql r"SELECT qty FROM orders" := rfl
def escaped := sql! shop "SELECT qty FROM orders; SELECT 'a\\nb', label FROM orders"
def finished : Nat := 0
'''


def test_column_hovers(runtime_root: Path, tmp_path: Path) -> None:
    """Our column information (`SqlNameInfo`, `SqlNameDescription`) reaches the real server: declared
    facts, constraints, affinity and collation for table columns; derived columns for WITH definitions,
    subqueries and views; the scope of aliases, joins and sequential schema changes."""
    server = LeanServer(runtime_root, tmp_path)
    try:
        uri = server.open(SOURCE)
        label = name_hover(server, uri, SOURCE, "label, qty", 0, "label")
        assert label.startswith("Column `label` of table `orders` (alias `o`)."), label
        assert "Declared type: TEXT." in label and "NOT NULL" in label, label
        assert "Affinity in comparisons: TEXT." in label and "Collation: NOCASE." in label, label
        qty = name_hover(server, uri, SOURCE, "qty FROM orders AS o", 0, "qty")
        assert "Declared type: INTEGER." in qty and "Constraints: none." in qty, qty
        assert "Collation: BINARY." in qty, qty
        order_id = name_hover(server, uri, SOURCE, "order_id, note", 0, "order_id")
        assert "FOREIGN KEY" in order_id, order_id
        assert "UNIQUE" in name_hover(server, uri, SOURCE, "note FROM lines", 0, "note")
        derived = name_hover(server, uri, SOURCE, "qty FROM w UNION", 0, "qty")
        assert derived.startswith("Column `qty` of WITH definition `w`."), derived
        assert "Derived column" in derived and "declared type of its base column is INTEGER" in derived, derived
        assert "WITH definition `w`" in name_hover(server, uri, SOURCE, "qty FROM w", 1, "qty")
        assert "subquery `s`" in name_hover(server, uri, SOURCE, "qty FROM (SELECT", 0, "qty")
        assert "Column `qty` of table `orders`." in name_hover(server, uri, SOURCE, "qty FROM orders) AS s", 0, "qty")
        view = name_hover(server, uri, SOURCE, "label FROM totals", 0, "label")
        assert "view `totals`" in view and "Collation: NOCASE." in view, view
        assert "Column `id` of table `orders`." in name_hover(server, uri, SOURCE, "id = o.id", 0, "id")
        assert "Column `id` of table `orders` (alias `o`)." in name_hover(server, uri, SOURCE, "id = order_id", 0, "id")
        first = name_hover(server, uri, SOURCE, "x FROM t;", 0, "x")
        assert "Declared type: INTEGER." in first, first
        assert "Declared type: TEXT." in name_hover(server, uri, SOURCE, "x FROM t\"", 0, "x")
    finally:
        server.close()


def comparison_hover(server: LeanServer, uri: str, expression: str, operator_offset: int) -> str:
    """The hover text at the operator of a comparison; the range must be the whole comparison."""
    start = position(SOURCE, expression)
    at = {**start, "character": start["character"] + operator_offset}
    result = server.request("textDocument/hover", {"textDocument": {"uri": uri}, "position": at})
    assert isinstance(result, dict), (expression, result)
    end = {**start, "character": start["character"] + len(expression)}
    assert result["range"] == {"start": start, "end": end}, result
    contents = result["contents"]
    assert isinstance(contents, dict) and isinstance(contents["value"], str), result
    return contents["value"]


def test_comparison_hovers(runtime_root: Path, tmp_path: Path) -> None:
    """Our comparison information (`SqlNameDescription.comparisonLine`) reaches the real server: the
    affinity that SQLite applies to the operands of `=`, `IN`, and `BETWEEN` (two lines), no affinity
    for a unary plus and a CAST, and the collation of the column."""
    server = LeanServer(runtime_root, tmp_path)
    try:
        uri = server.open(SOURCE)
        both = comparison_hover(server, uri, "qty IN (1, 2)", 4)
        assert "applies INTEGER affinity" in both, both
        cast = comparison_hover(server, uri, "CAST(qty AS TEXT) = 'x'", 17)
        assert "applies TEXT affinity" in cast, cast
        unary = comparison_hover(server, uri, "+qty = 1", 5)
        assert "applies no affinity" in unary, unary
        bounds = comparison_hover(server, uri, "qty BETWEEN 1 AND price", 5)
        assert "lower bound" in bounds and "upper bound" in bounds and bounds.count("\n") == 1, bounds
    finally:
        server.close()


def test_tokens_and_exclusions(runtime_root: Path, tmp_path: Path) -> None:
    """Our semantic tokens and exclusions (`SqlNameInfo.emitNameSite`): a found column is a `variable`
    token at its exact range, a view column named by an alias is described, and an ambiguous name, a
    name in plain `sql`, a name in an escaped literal, and keywords get no hover or token. The
    ambiguous name is the only error of the fixture, so the editor information leaves the term of a
    checked `sql!` equal to the term of `sql` (the `example` of the fixture)."""
    server = LeanServer(runtime_root, tmp_path)
    try:
        uri = server.open(SOURCE)
        tokens = semantic_tokens(server, uri)
        for spelling, occurrence, token in (("label, qty", 0, "label"), ("qty FROM orders AS o", 0, "qty"),
                                            ("note FROM lines", 0, "note"), ("next, key", 0, "next")):
            start = position(SOURCE, spelling, occurrence)
            assert (start["line"], start["character"], len(token), "variable") in tokens, (spelling, tokens)
        assert "view `totals`" in name_hover(server, uri, SOURCE, "next, key", 0, "next")
        assert "Derived column" in name_hover(server, uri, SOURCE, "key FROM totals", 0, "key")
        for spelling, occurrence in (("id FROM orders, orders", 0), ('qty FROM orders"', 0),
                                 ("qty FROM orders; SELECT", 0), ('label FROM orders"', 0)):
            assert "Column `" not in hover_text_or_none(server, uri, SOURCE, spelling, occurrence), spelling
            start = position(SOURCE, spelling, occurrence)
            assert not any(line == start["line"] and column == start["character"]
                           for line, column, _, _ in tokens), spelling
        plain = position(SOURCE, "def plain")["line"]
        escaped = position(SOURCE, "def escaped")["line"]
        assert not [token for token in tokens if token[0] in (plain, escaped) and token[3] == "variable"], tokens
        problems = diagnostics(server, uri)
        assert len(problems) == 1 and "ambiguous" in problems[0]["message"], problems
    finally:
        server.close()
