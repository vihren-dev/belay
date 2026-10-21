"""The mapping of `PRAGMA foreign_keys` to Syntax JSON (`belay.sqlite.syntax_pragmas`).

ADR 0018, D4: the frontend maps the query form and each value that SQLite's
`sqlite3GetBoolean` reads as on or off, and refuses every other pragma, a schema name and any
other value, which the model does not describe.
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


def test_foreign_keys_pragma_keeps_its_value(parse_sql: Callable[..., Tree]) -> None:
    """`pragma` maps the query form to no value and each boolean form to its value, with the
    name and the words in either ASCII case and quoted words dequoted."""
    sql = ("PRAGMA foreign_keys; PRAGMA foreign_keys = ON; PRAGMA FOREIGN_KEYS = off; PRAGMA foreign_keys(1); "
           "PRAGMA foreign_keys = 0; PRAGMA foreign_keys = 'Yes'; PRAGMA foreign_keys = no; PRAGMA foreign_keys = TRUE; "
           "PRAGMA \"foreign_keys\" = false;")
    assert mapped(parse_sql, sql) == [{"pragmaForeignKeys": {"value": value}}
                                      for value in (None, True, False, True, False, True, False, True, False)]


@pytest.mark.parametrize(("sql", "message"), [
    ("PRAGMA journal_mode;", "Only PRAGMA foreign_keys is modeled"),
    ("PRAGMA main.foreign_keys = ON;", "Only PRAGMA foreign_keys is modeled"),
    ("PRAGMA foreign_keys = 2;", "Only on, off, yes, no, true, false, 0 and 1"),
    ("PRAGMA foreign_keys = -1;", "Only on, off, yes, no, true, false, 0 and 1"),
    ("PRAGMA foreign_keys = full;", "Only on, off, yes, no, true, false, 0 and 1"),
])
def test_other_pragmas_and_values_are_refused(parse_sql: Callable[..., Tree], sql: str, message: str) -> None:
    """`pragma` refuses another pragma, a schema name and a value that is not one of the modeled
    words or numbers, with its source range."""
    with pytest.raises(SqlError) as raised:
        statements(parse_sql(sql))
    assert raised.value.status == "UNSUPPORTED" and message in str(raised.value)
