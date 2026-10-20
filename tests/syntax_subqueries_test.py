"""The frontend lifts the subqueries of a statement into its list (`belay.sqlite.syntax_subqueries`).

These tests check the JSON that Lean's `Syntax.Subquery` decoder reads: the forms that name
a subquery by its index, the order of the list and the query around each subquery, the
source range of a subquery's clauses, the subqueries of writes, and the refusal of a subquery
where the model does not place it (ADR 0018, D1).
"""

from collections.abc import Callable

import pytest

from belay.sqlite.errors import SqlError
from belay.sqlite.sql_tree import Tree
from belay.sqlite.syntax import statements

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def column(name: str) -> dict[str, object]:
    """The JSON of an identifier written without double quotes."""
    return {"identifier": {"name": name, "quote": "none"}}


def test_forms_name_subqueries_in_text_order(parse_sql: Callable[..., Tree]) -> None:
    """EXISTS, NOT IN and a scalar subquery name the subqueries 0, 1 and 2 in the order of their
    text; NOT EXISTS is NOT of EXISTS, and each subquery keeps its clauses."""
    [statement] = [item.value for item in statements(parse_sql(
        "SELECT (SELECT max(b) FROM u) FROM t WHERE NOT EXISTS (SELECT 1 FROM u WHERE u.b = t.a) "
        "AND a NOT IN (SELECT b FROM u);"))]
    select = statement["select"]
    assert select["columns"][0]["expression"]["value"] == {"subquery": {"index": 0}}
    assert select["filter"] == {"and": {
        "left": {"not": {"operand": {"exists": {"index": 1}}}},
        "right": {"inQuery": {"operand": column("a"), "index": 2, "negated": True}}}}
    first, second, third = select["subqueries"]
    assert first["columns"] == [{"expression": {"value": {"call": {"name": "max", "arguments": [column("b")]}},
                                                "alias": None, "text": "max(b)"}}]
    assert second["filter"] == {"compare": {"operator": "eq", "left": {"qualified": {"source": "u", "column": "b"}},
                                            "right": {"qualified": {"source": "t", "column": "a"}}}}
    assert third["source"] == {"table": "u", "alias": None, "arguments": None}
    assert [item["parent"] for item in (first, second, third)] == [None, None, None]


def test_nested_subqueries_name_the_query_around_them(parse_sql: Callable[..., Tree]) -> None:
    """A subquery inside a subquery comes after it and names it as its parent; a later
    subquery of the statement's query comes after both."""
    [statement] = [item.value for item in statements(parse_sql(
        "SELECT 1 FROM t WHERE EXISTS (SELECT 1 FROM u WHERE b IN (SELECT a FROM t)) AND EXISTS (SELECT 2);"))]
    subqueries = statement["select"]["subqueries"]
    assert [item["parent"] for item in subqueries] == [None, 0, None]
    assert subqueries[0]["filter"] == {"inQuery": {"operand": column("b"), "index": 1, "negated": False}}
    assert subqueries[2]["source"] is None


def test_subquery_paths_select_their_text(parse_sql: Callable[..., Tree]) -> None:
    """A Lean issue path into a subquery, `[8, index, clause, ...]`, selects the text of that
    clause, so a restriction in a subquery points at it."""
    sql = "SELECT a FROM t WHERE EXISTS (SELECT 1 FROM u WHERE b = a);"
    [statement] = statements(parse_sql(sql))
    start, end = statement.span([8, 0, 3])
    assert sql.encode()[start:end].decode() == "b = a"


def test_writes_list_the_subqueries_of_their_expressions(parse_sql: Callable[..., Tree]) -> None:
    """INSERT VALUES, UPDATE SET and WHERE, and DELETE WHERE list their subqueries in the
    `subqueries` field, after `returning`, with the write as the query around them."""
    [insert, update, delete] = [item.value for item in statements(parse_sql(
        "INSERT INTO t VALUES ((SELECT max(b) FROM u)); UPDATE t SET a = (SELECT 1) WHERE EXISTS (SELECT 2); "
        "DELETE FROM t WHERE a IN (SELECT b FROM u);"))]
    assert insert["insert"]["rows"] == [[{"subquery": {"index": 0}}]]
    assert [item["parent"] for item in insert["insert"]["subqueries"]] == [None]
    assert update["update"]["assignments"] == [["a", {"subquery": {"index": 0}}]]
    assert update["update"]["filter"] == {"exists": {"index": 1}}
    assert len(update["update"]["subqueries"]) == 2
    assert delete["delete"]["filter"] == {"inQuery": {"operand": column("a"), "index": 0, "negated": False}}
    assert list(delete["delete"]) == ["table", "filter", "returning", "subqueries"]


@pytest.mark.parametrize(("sql", "refused"), [
    ("UPDATE t SET a = 1 RETURNING (SELECT 1);", "SELECT 1"),
    ("INSERT INTO t VALUES (1) ON CONFLICT DO UPDATE SET a = (SELECT 1);", "SELECT 1"),
    ("CREATE TABLE c(a CHECK (a IN (SELECT 1)));", "SELECT 1"),
    ("SELECT a FROM t WHERE a IN u;", "a IN u"),
])
def test_subqueries_outside_their_clauses_are_refused(parse_sql: Callable[..., Tree], sql: str, refused: str) -> None:
    """A subquery in RETURNING, ON CONFLICT or a schema statement, and `x IN table`, have no
    constructor and are refused at their range."""
    with pytest.raises(SqlError) as raised:
        statements(parse_sql(sql))
    assert raised.value.status == "UNSUPPORTED"
    assert sql.encode()[raised.value.start:raised.value.end].decode() == refused
