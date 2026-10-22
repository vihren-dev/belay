"""The translation maps CHECK, CONSTRAINT names, foreign keys and generated columns
(`packages/belay-sqlite-text/Belay/Sqlite/Translation/Constraints.lean`, through the text package's program).

These tests check, against the pinned parser library, the label that the translation gives
each CHECK, as SQLite's parser tracks the constraint name in effect, and the column lists
that foreign keys keep (ADR 0014, slice 4).
"""

from collections.abc import Callable

import pytest
from conformance.sql_text import Translation


pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def mapped(parse_sql: Callable[..., Translation], sql: str) -> list[object]:
    """Return the syntax JSON of every statement of the SQL."""
    return [item.value for item in parse_sql(sql).statements()]


def test_checks_names_and_foreign_keys(parse_sql: Callable[..., Translation]) -> None:
    """CHECK maps with SQLite's label: the `CONSTRAINT` name in effect, which reaches from
    the last column into the table constraints until a comma, else the trimmed text,
    dequoted when it starts with a quote; foreign keys keep their column lists and their
    actions, a later clause replacing an earlier one (ADR 0014, slice 4)."""
    sql = ("CREATE TABLE t(a CONSTRAINT x NOT NULL CHECK (  a > 0 ) REFERENCES p(q) ON DELETE CASCADE "
           "ON UPDATE SET NULL ON DELETE RESTRICT, "
           "b CHECK (\"b\" < 3), CONSTRAINT y UNIQUE (b) CHECK (b != 1), CHECK (b > a) ON CONFLICT IGNORE, "
           "FOREIGN KEY (a, b) REFERENCES p(q, r) MATCH FULL);"
           "CREATE TABLE u(a CONSTRAINT z CHECK (a > 0), CHECK (a < 9), CHECK (a != 5));")
    first, second = mapped(parse_sql, sql)
    columns, constraints = first["createTable"]["columns"], first["createTable"]["constraints"]
    assert [constraint for constraint in columns[0]["constraints"] if "check" not in constraint] == [
        {"notNull": {"algorithm": None}},
        {"references": {"table": "p", "columns": ["q"], "onDelete": "restrict", "onUpdate": "setNull"}}]
    labels = [item["check"]["label"] for item in columns[0]["constraints"] + columns[1]["constraints"] + constraints
              if "check" in item]
    assert labels == ["x", "b", "y", "b > a"]
    assert constraints[-1] == {"foreignKey": {"columns": ["a", "b"], "table": "p", "referenced": ["q", "r"],
                                              "onDelete": "noAction", "onUpdate": "noAction"}}
    assert [item["check"]["label"] for item in second["createTable"]["constraints"]] == ["z", "a != 5"]


def test_deferral_clauses_are_constraints_of_their_own(parse_sql: Callable[..., Translation]) -> None:
    """A deferral clause maps to `deferral`, after the constraint that it follows, deferred only
    for `DEFERRABLE INITIALLY DEFERRED` (ADR 0018, D4): in a column definition, as SQLite's
    grammar has it, and after a FOREIGN KEY table constraint."""
    sql = ("CREATE TABLE t(a REFERENCES p DEFERRABLE INITIALLY DEFERRED NOT DEFERRABLE INITIALLY DEFERRED, "
           "b DEFERRABLE, FOREIGN KEY (a) REFERENCES p DEFERRABLE INITIALLY DEFERRED, "
           "FOREIGN KEY (b) REFERENCES p DEFERRABLE INITIALLY IMMEDIATE, FOREIGN KEY (a) REFERENCES p);")
    (table,) = mapped(parse_sql, sql)
    columns, constraints = table["createTable"]["columns"], table["createTable"]["constraints"]
    assert [list(item) for item in columns[0]["constraints"]] == [["references"], ["deferral"], ["deferral"]]
    assert [item["deferral"]["deferred"] for item in columns[0]["constraints"][1:]] == [True, False]
    assert columns[1]["constraints"] == [{"deferral": {"deferred": False}}]
    assert [list(item)[0] for item in constraints] == ["foreignKey", "deferral", "foreignKey", "deferral", "foreignKey"]
    assert [constraints[1]["deferral"]["deferred"], constraints[3]["deferral"]["deferred"]] == [True, False]


def test_generated_columns_keep_their_kind_and_sqlite_type(parse_sql: Callable[..., Translation]) -> None:
    """`AS (expr)` maps with its kind token as written, quotes included, or none, which
    resolution reads, and the declared type as `sqlite3AddColumn` leaves it: a trailing
    `GENERATED ALWAYS` goes, then the type is dequoted (ADR 0014, slice 5)."""
    (table,) = mapped(parse_sql, "CREATE TABLE t(a INTEGER, b TEXT GENERATED ALWAYS AS (a) stored, c AS (a), "
                                 "d AS (a) \"stored\");")
    columns = table["createTable"]["columns"]
    a = {"identifier": {"name": "a", "quote": "none"}}
    assert [(column["declaredType"], column["constraints"]) for column in columns[1:]] == [
        ("TEXT", [{"generated": {"expression": a, "kind": "stored"}}]),
        (None, [{"generated": {"expression": a, "kind": None}}]),
        (None, [{"generated": {"expression": a, "kind": '"stored"'}}])]


@pytest.mark.parametrize(("written", "reported"), [
    ("TEXT GENERATED ALWAYS", "TEXT"), ("foogenerated always", "foo"),
    ("TEXT GENERATED /*x*/ ALWAYS", "TEXT GENERATED /*x*/"), ("GENERATED ALWAYS", ""), ("always", "always"),
    ("\u00e9\u00e9\u00e9\u00e9\u00e9always", "\u00e9\u00e9\u00e9\u00e9\u00e9"),
    ('"TEXT GENERATED ALWAYS"', "TEXT GENERATED ALWAYS"), ('"Big" GENERATED ALWAYS', "Big"),
    ("'Odd''Q' GENERATED ALWAYS", "Odd'Q")])
def test_declared_type_follows_sqlite(parse_sql: Callable[..., Translation], written: str, reported: str) -> None:
    """The type rule of `sqlite3AddColumn`, each case checked natively with 3.51.0: the word
    length counts UTF-8 bytes, the words compare in either ASCII case, a comment between
    them keeps them, and a quoted type keeps them, as it ends with its quote."""
    (table,) = mapped(parse_sql, f"CREATE TABLE t(a {written});")
    assert table["createTable"]["columns"][0]["declaredType"] == reported
