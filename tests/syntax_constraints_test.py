"""The frontend maps CHECK, CONSTRAINT names, foreign keys and generated columns
(`belay.sqlite.syntax_constraints`).

These tests check, against the pinned parser library, the label that the frontend gives
each CHECK, as SQLite's parser tracks the constraint name in effect, and the column lists
that foreign keys keep (ADR 0014, slice 4).
"""

from collections.abc import Callable

import pytest

from belay.sqlite.sql_tree import Tree
from belay.sqlite.syntax import statements

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def mapped(parse_sql: Callable[..., Tree], sql: str) -> list[object]:
    """Return the syntax JSON of every statement of the SQL."""
    return [item.value for item in statements(parse_sql(sql))]


def test_checks_names_and_foreign_keys(parse_sql: Callable[..., Tree]) -> None:
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


def test_generated_columns_keep_their_kind_and_type_as_written(parse_sql: Callable[..., Tree]) -> None:
    """`AS (expr)` maps with its kind token as written, quotes included, or none, and the
    declared type as written, `GENERATED ALWAYS` included: resolution decides both
    (ADR 0014, slice 5)."""
    (table,) = mapped(parse_sql, "CREATE TABLE t(a INTEGER, b TEXT GENERATED ALWAYS AS (a) stored, c AS (a), "
                                 "d AS (a) \"stored\");")
    columns = table["createTable"]["columns"]
    a = {"identifier": {"name": "a", "quote": "none"}}
    assert [(column["declaredType"], column["constraints"]) for column in columns[1:]] == [
        ("TEXT GENERATED ALWAYS", [{"generated": {"expression": a, "kind": "stored"}}]),
        (None, [{"generated": {"expression": a, "kind": None}}]),
        (None, [{"generated": {"expression": a, "kind": '"stored"'}}])]
