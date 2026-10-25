"""The translation maps the schema name `before` of a source and of a qualified column to the `schema` field
(`sourceSchema` in `packages/belay-sqlite-text/Belay/Sqlite/Translation/Sources.lean` and `queryExpressionWith` in
`QueryExpression.lean`, ADR 0017, S6), and refuses every other schema name at its byte range."""

from collections.abc import Callable

import pytest

from belay.sqlite.errors import SqlError
from conformance.sql_text import Translation

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def test_the_initial_schema_before_maps_to_a_schema_field(parse_sql: Callable[..., Translation]) -> None:
    """`sourceSchema` and `queryExpressionWith`: the schema name
    `before`, written in any letter case, is the `schema` of a table source and of a qualified column
    (ADR 0017, S6); an alias and a quoted name containing a dot keep their ordinary two-part forms."""
    [query] = [item.value for item in parse_sql(
        'SELECT before.t.a, BEFORE.x.b, before.a, "before.t".a FROM before.t, Before.u AS x, t AS before;').statements()]
    select = query["select"]
    assert [item["expression"]["value"] for item in select["columns"]] == [
        {"qualified": {"source": "t", "column": "a", "schema": "before"}},
        {"qualified": {"source": "x", "column": "b", "schema": "BEFORE"}},
        {"qualified": {"source": "before", "column": "a", "schema": None}},
        {"qualified": {"source": "before.t", "column": "a", "schema": None}}]
    assert select["source"] == {"table": "t", "alias": None, "arguments": None, "query": None, "schema": "before"}
    assert [join["source"] for join in select["joins"]] == [
        {"table": "u", "alias": "x", "arguments": None, "query": None, "schema": "Before"},
        {"table": "t", "alias": "before", "arguments": None, "query": None, "schema": None}]


@pytest.mark.parametrize(("sql", "refused"), [
    ("SELECT temp.t.a FROM t;", "temp.t.a"), ("SELECT a FROM temp.t;", ".t"),
    ("SELECT a FROM main.json_each('[1]');", ".json_each"),
])
def test_a_schema_name_other_than_before_is_unsupported(
        parse_sql: Callable[..., Translation], sql: str, refused: str) -> None:
    """`sourceSchema` and `queryExpressionWith` accept only `before` as a schema name of a source or a column;
    every other schema name is refused at the range of the refused syntax."""
    with pytest.raises(SqlError) as raised:
        parse_sql(sql).statements()
    assert raised.value.status == "UNSUPPORTED"
    assert sql.encode()[raised.value.start:raised.value.end].decode() == refused
