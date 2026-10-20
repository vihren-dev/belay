"""The mapping of DROP TABLE and DROP INDEX to Syntax JSON (`belay.sqlite.syntax_drops`).

ADR 0014, slice 7: the frontend keeps the name as written and `IF EXISTS` as a flag, and
refuses a schema name, which the model does not describe.
"""

from collections.abc import Callable

import pytest

from belay.sqlite.errors import SqlError
from belay.sqlite.sql_tree import Tree
from belay.sqlite.syntax import statements

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def mapped(parse_sql: Callable[..., Tree], sql: str) -> list[object]:
    """Return the syntax JSON of every statement of the SQL."""
    return [item.value for item in statements(parse_sql(sql))]


def test_drops_keep_the_name_and_if_exists(parse_sql: Callable[..., Tree]) -> None:
    """`drop` maps each form to its constructor, with the dequoted name and `ifExists`."""
    sql = 'DROP TABLE [Big T]; DROP TABLE IF EXISTS t; DROP INDEX "I"; drop index if exists i;'
    assert mapped(parse_sql, sql) == [
        {"dropTable": {"name": "Big T", "ifExists": False}}, {"dropTable": {"name": "t", "ifExists": True}},
        {"dropIndex": {"name": "I", "ifExists": False}}, {"dropIndex": {"name": "i", "ifExists": True}}]


@pytest.mark.parametrize("sql", ["DROP TABLE main.t;", "DROP INDEX IF EXISTS temp.i;"])
def test_drop_with_a_schema_name_is_refused(parse_sql: Callable[..., Tree], sql: str) -> None:
    """`drop` refuses a schema name at its range, as the other statements do."""
    with pytest.raises(SqlError) as raised:
        statements(parse_sql(sql))
    assert raised.value.status == "UNSUPPORTED"
    assert "A schema name is not modeled" in str(raised.value)
