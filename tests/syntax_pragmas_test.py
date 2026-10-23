"""The mapping of the pragmas of the model to Syntax JSON (`pragma` in
`packages/belay-sqlite-text/Belay/Sqlite/Translation/Schema.lean`, through the text package's program).

ADR 0018, D4 and ADR 0019, D2: the translation maps the query form of `PRAGMA foreign_keys` and
each value that SQLite's `sqlite3GetBoolean` reads as on or off, and the table name of
`PRAGMA table_info` and `PRAGMA foreign_key_list`. It refuses every other pragma, a schema name
and any other value, which the model does not describe.
"""

from collections.abc import Callable

import pytest

from belay.sqlite.errors import SqlError
from conformance.sql_text import Translation

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def mapped(parse_sql: Callable[..., Translation], sql: str) -> list[object]:
    """Return the syntax JSON of every statement of the SQL."""
    return [item.value for item in parse_sql(sql).statements()]


def pragma(form: dict[str, object]) -> dict[str, object]:
    """Return the syntax JSON of a pragma statement with the form."""
    return {"pragma": {"pragma": form}}


def test_foreign_keys_pragma_keeps_its_value(parse_sql: Callable[..., Translation]) -> None:
    """`pragma` maps the query form to no value and each boolean form to its value, with the
    name and the words in either ASCII case and quoted words dequoted."""
    sql = ("PRAGMA foreign_keys; PRAGMA foreign_keys = ON; PRAGMA FOREIGN_KEYS = off; PRAGMA foreign_keys(1); "
           "PRAGMA foreign_keys = 0; PRAGMA foreign_keys = 'Yes'; PRAGMA foreign_keys = no; PRAGMA foreign_keys = TRUE; "
           "PRAGMA \"foreign_keys\" = false;")
    assert mapped(parse_sql, sql) == [pragma({"setting": {"setting": "foreignKeys", "value": value}})
                                      for value in (None, True, False, True, False, True, False, True, False)]


def test_schema_pragmas_keep_the_table_name(parse_sql: Callable[..., Translation]) -> None:
    """`pragma` maps `table_info` and `foreign_key_list` with the table name in parentheses or
    after `=`, as a name or a string, without its quotes, and the pragma name in any case."""
    sql = ("PRAGMA table_info(t); PRAGMA TABLE_INFO = 'My T'; PRAGMA table_info(\"x\"\"y\"); "
           "PRAGMA foreign_key_list(c); PRAGMA Foreign_Key_List = [c];")
    assert mapped(parse_sql, sql) == [
        pragma({"tableInfo": {"table": "t"}}), pragma({"tableInfo": {"table": "My T"}}),
        pragma({"tableInfo": {"table": "x\"y"}}), pragma({"foreignKeyList": {"table": "c"}}),
        pragma({"foreignKeyList": {"table": "c"}})]


@pytest.mark.parametrize(("sql", "message"), [
    ("PRAGMA journal_mode;", "Only PRAGMA foreign_keys, table_info and foreign_key_list are modeled"),
    ("PRAGMA main.foreign_keys = ON;", "without a schema name"),
    ("PRAGMA main.table_info(t);", "without a schema name"),
    ("PRAGMA foreign_keys = 2;", "Only on, off, yes, no, true, false, 0 and 1"),
    ("PRAGMA foreign_keys = -1;", "Only on, off, yes, no, true, false, 0 and 1"),
    ("PRAGMA foreign_keys = full;", "Only on, off, yes, no, true, false, 0 and 1"),
    ("PRAGMA table_info;", "Write the table name in parentheses"),
    ("PRAGMA table_info(1);", "Only a table name is modeled"),
    ("PRAGMA foreign_key_list(-1);", "Only a table name is modeled"),
    ("PRAGMA table_info(ON);", "Only a table name is modeled"),
])
def test_other_pragmas_and_values_are_refused(parse_sql: Callable[..., Translation], sql: str, message: str) -> None:
    """`pragma` refuses another pragma, a schema name and a value that is not one of the modeled
    words, numbers or names, with its source range."""
    with pytest.raises(SqlError) as raised:
        parse_sql(sql).statements()
    assert raised.value.status == "UNSUPPORTED" and message in str(raised.value)
