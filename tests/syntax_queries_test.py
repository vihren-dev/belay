"""The frontend maps a single-table SELECT to statement syntax (`belay.sqlite.syntax_queries`).

These tests check the JSON that Lean's `Syntax.Statement.select` decoder reads, the
source text of result columns, the LIMIT forms, and the refusal of query syntax
outside slice 1 of ADR 0012 with its byte range.
"""

from collections.abc import Callable

import pytest

from belay.sqlite.errors import SqlError
from belay.sqlite.sql_tree import Tree
from belay.sqlite.syntax import statements

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def column(name: str) -> dict[str, object]:
    """The JSON of an identifier written without double quotes."""
    return {"identifier": {"name": name, "doubleQuoted": False}}


def test_select_keeps_columns_text_and_clauses(parse_sql: Callable[..., Tree]) -> None:
    """Every clause maps; a result column keeps its alias and its source text exactly."""
    [select] = [item.value for item in statements(parse_sql(
        "SELECT *, a AS x, count(*), min(b), b  <>  1 FROM t WHERE a IS NOT NULL AND NOT b < 2 "
        "GROUP BY a ORDER BY 1 DESC, b LIMIT 1, 2;"))]
    assert select == {"select": {
        "columns": ["star",
                    {"expression": {"value": column("a"), "alias": "x", "text": "a"}},
                    {"expression": {"value": {"callStar": {"name": "count"}}, "alias": None, "text": "count(*)"}},
                    {"expression": {"value": {"call": {"name": "min", "operand": column("b")}},
                                    "alias": None, "text": "min(b)"}},
                    {"expression": {"value": {"compare": {"operator": "ne", "left": column("b"),
                                                          "right": {"numeric": {"text": "1"}}}},
                                    "alias": None, "text": "b  <>  1"}}],
        "table": "t",
        "filter": {"and": {"left": {"compare": {"operator": "isNot", "left": column("a"), "right": "null"}},
                           "right": {"not": {"operand": {"compare": {"operator": "lt", "left": column("b"),
                                                                     "right": {"numeric": {"text": "2"}}}}}}}},
        "groupBy": [column("a")],
        "orderBy": [{"expression": {"numeric": {"text": "1"}}, "descending": True},
                    {"expression": column("b"), "descending": False}],
        "limit": {"numeric": {"text": "2"}}, "offset": {"numeric": {"text": "1"}}}}


@pytest.mark.parametrize(("sql", "operand"), [
    ("SELECT a FROM t WHERE a ISNULL;", False), ("SELECT a FROM t WHERE a NOTNULL;", True),
    ("SELECT a FROM t WHERE a NOT NULL;", True),
])
def test_postfix_null_tests_map_to_is_null(parse_sql: Callable[..., Tree], sql: str, operand: bool) -> None:
    """`ISNULL`, `NOTNULL` and `NOT NULL` are `IS NULL` and its negation."""
    [select] = [item.value for item in statements(parse_sql(sql))]
    assert select["select"]["filter"] == {"isNull": {"operand": column("a"), "negated": operand}}


@pytest.mark.parametrize(("sql", "refused"), [
    ("SELECT 1;", "SELECT 1"), ("SELECT DISTINCT a FROM t;", "DISTINCT"),
    ("SELECT a FROM t GROUP BY a HAVING a > 1;", "HAVING a > 1"), ("SELECT t.* FROM t;", "t.*"),
    ("SELECT a FROM t, u;", "t,"), ("SELECT a FROM t ORDER BY a NULLS LAST;", "NULLS LAST"),
    ("SELECT substr(a, 1) FROM t;", "substr(a, 1)"), ("SELECT count(DISTINCT a) FROM t;", "DISTINCT"),
    ("SELECT a FROM t UNION SELECT a FROM t;", "SELECT a FROM t UNION SELECT a FROM t"),
    ("SELECT a + 1 FROM t;", "a + 1"), ("SELECT a FROM t AS s;", "AS s"),
])
def test_query_syntax_outside_the_slice_is_unsupported_at_its_range(
        parse_sql: Callable[..., Tree], sql: str, refused: str) -> None:
    """Each refusal is UNSUPPORTED, and its byte range is the refused syntax."""
    with pytest.raises(SqlError) as raised:
        statements(parse_sql(sql))
    assert raised.value.status == "UNSUPPORTED"
    assert sql.encode()[raised.value.start:raised.value.end].decode() == refused


def test_query_expressions_stay_refused_in_writes(parse_sql: Callable[..., Tree]) -> None:
    """Comparisons and aggregates are query syntax: a VALUES row keeps refusing them."""
    with pytest.raises(SqlError, match="Unsupported expression"):
        statements(parse_sql("INSERT INTO t VALUES (a < 1);"))
