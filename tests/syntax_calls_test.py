"""The frontend maps function calls to statement syntax (`belay.sqlite.syntax_queries`).

These tests check the JSON that Lean's `Syntax.Expr` decoder reads for calls without
arguments, with one argument and with several, and for the JSON operators, which SQLite's
parser makes calls (ADR 0012, slices 2, 6b and 6f).
"""

from collections.abc import Callable

import pytest

from belay.sqlite.sql_tree import Tree
from belay.sqlite.syntax import statements

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def column(name: str) -> dict[str, object]:
    """The JSON of an identifier written without double quotes."""
    return {"identifier": {"name": name, "quote": "none"}}


def test_call_without_arguments_has_an_empty_list(parse_sql: Callable[..., Tree]) -> None:
    """A call without arguments, such as `date()` or `random()`, is a `call` with an empty
    argument list and its name as written (ADR 0013, D3); resolution decides whether the
    model has the function."""
    [select] = [item.value for item in statements(parse_sql("SELECT Date(), random();"))]
    assert [column["expression"]["value"] for column in select["select"]["columns"]] == [
        {"call": {"name": "Date", "arguments": []}}, {"call": {"name": "random", "arguments": []}}]


def test_numbers_map_arithmetic_cast_and_call_chains(parse_sql: Callable[..., Tree]) -> None:
    """Arithmetic, unary minus of an expression, CAST with its type name as written, and a
    call with three arguments as one list (ADR 0012, slice 2; ADR 0013, D3)."""
    [select] = [item.value for item in statements(parse_sql(
        "SELECT -(a % 2) * b, CAST(a AS Varchar(10)), Coalesce(a, b, 3) FROM t;"))]
    values = [column["expression"]["value"] for column in select["select"]["columns"]]
    remainder = {"arithmetic": {"operator": "remainder", "left": column("a"), "right": {"numeric": {"text": "2"}}}}
    assert values[0] == {"arithmetic": {"operator": "multiply", "left": {"negate": {"operand": remainder}},
                                        "right": column("b")}}
    assert values[1] == {"cast": {"operand": column("a"), "typeName": "Varchar(10)"}}
    assert values[2] == {"call": {"name": "Coalesce",
                                  "arguments": [column("a"), column("b"), {"numeric": {"text": "3"}}]}}


def test_json_operators_and_nested_calls_map_to_calls(parse_sql: Callable[..., Tree]) -> None:
    """`->` and `->>` are a `call` of the function with the operator's text as its name and
    two arguments, and a nested call stays a nested argument, distinct from a call of three
    arguments (`syntax_queries.query_expression`, `syntax_queries.call`; ADR 0012, slice 6b)."""
    [select] = [item.value for item in statements(parse_sql(
        "SELECT a -> '$.x', a ->> 'y', json_extract(a, json_extract(b, c)), json_extract(a, b, c) FROM t;"))]
    values = [column["expression"]["value"] for column in select["select"]["columns"]]
    assert values[0] == {"call": {"name": "->", "arguments": [column("a"), {"string": {"bytes": list(b"$.x")}}]}}
    assert values[1] == {"call": {"name": "->>", "arguments": [column("a"), {"string": {"bytes": list(b"y")}}]}}
    assert values[2] == {"call": {"name": "json_extract", "arguments": [
        column("a"), {"call": {"name": "json_extract", "arguments": [column("b"), column("c")]}}]}}
    assert values[3] == {"call": {"name": "json_extract", "arguments": [column("a"), column("b"), column("c")]}}
