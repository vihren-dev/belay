"""The mapping of the CREATE TABLE options to Syntax JSON (`tableOptions` in `packages/belay-sqlite-text/Belay/Sqlite/Translation/Tables.lean`,
through the text package's program).

ADR 0014 adds `WITHOUT ROWID` (slice 2) and `STRICT` (slice 6). SQLite's grammar reads each
option word as written, in either ASCII case, and refuses any other word, also a quoted one,
with `unknown table option`; the translation must map the same words and refuse the others.
"""

from collections.abc import Callable

import pytest

from belay.sqlite.errors import SqlError
from conformance.sql_text import Translation

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def mapped(parse_sql: Callable[..., Translation], sql: str) -> list[object]:
    """Return the syntax JSON of every statement of the SQL."""
    return [item.value for item in parse_sql(sql).statements()]


@pytest.mark.parametrize(("options", "expected"), [
    ("", {"withoutRowid": False}),
    ("STRICT", {"withoutRowid": False, "strict": True}),
    ("sTrIcT, without ROWID", {"withoutRowid": True, "strict": True}),
    ("WITHOUT rowid", {"withoutRowid": True}),
])
def test_table_options_map_strict_and_without_rowid(parse_sql: Callable[..., Translation], options: str,
                                                    expected: dict[str, bool]) -> None:
    """`table_options` reads `STRICT` and `WITHOUT ROWID` in either ASCII case, as SQLite's
    grammar does, and writes `strict` only for a `STRICT` table, so other records keep
    their form."""
    statement = mapped(parse_sql, f"CREATE TABLE t(a INTEGER PRIMARY KEY) {options};")[0]
    assert statement["createTable"]["options"] == expected


@pytest.mark.parametrize("option", ['"strict"', "[STRICT]", 'WITHOUT "rowid"', "STRICTER", "WITHOUT oid"])
def test_other_table_options_are_refused(parse_sql: Callable[..., Translation], option: str) -> None:
    """`table_options` refuses a quoted option word and any other word: SQLite compares the
    token as written, so a quoted word is its `unknown table option` error."""
    sql = f"CREATE TABLE t(a INTEGER PRIMARY KEY) {option};"
    with pytest.raises(SqlError) as raised:
        parse_sql(sql).statements()
    assert raised.value.status == "UNSUPPORTED"
    assert "use WITHOUT ROWID or STRICT" in str(raised.value)
