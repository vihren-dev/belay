"""The translation maps parser productions to statement syntax and keeps source ranges.

These tests check `packages/belay-sqlite-text/Belay/Sqlite/Translation` through the text
package's program: the JSON that Lean's `Syntax.Statement` decoder reads, the lexical decoding of
names and literals, and the refusal of syntax without a constructor at its range.
`tests/surface/TranslationChecks.lean` checks the range that a Lean node path selects and the
lexical helpers.
"""

from collections.abc import Callable

import pytest

from belay.sqlite.errors import SqlError
from conformance.sql_text import Translation

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_native]


def mapped(parse_sql: Callable[..., Translation], sql: str) -> list[object]:
    """Return the syntax JSON of every statement of the SQL."""
    return [item.value for item in parse_sql(sql).statements()]


def column(name: str, declared: str | None, constraints: list[object] | None = None) -> dict[str, object]:
    """The JSON of one column definition."""
    return {"name": name, "declaredType": declared, "constraints": constraints or []}


def test_definitions_keep_names_types_and_constraints_as_written(parse_sql: Callable[..., Translation]) -> None:
    """Names keep their case, types keep SQLite's dequoted span, and every constraint maps."""
    sql = ('CREATE TABLE [Big T](a VARCHAR ( 10 ) NOT NULL PRIMARY KEY DESC, "B" "Some" Type UNIQUE, '
           "c DEFAULT -1, d DEFAULT CURRENT_TIMESTAMP, e DEFAULT 'x''y', f, PRIMARY KEY(a), UNIQUE(c, d));"
           "CREATE UNIQUE INDEX i ON `Big T`(a, B); ALTER TABLE t ADD COLUMN z INT DEFAULT y;")
    assert mapped(parse_sql, sql) == [
        {"createTable": {"name": "Big T", "columns": [
            column("a", "VARCHAR ( 10 )", [{"notNull": {"algorithm": None}},
                                           {"primaryKey": {"descending": True, "algorithm": None}}]),
            column("B", "Some", [{"unique": {"algorithm": None}}]),
            column("c", None, [{"default": {"sourceText": "-1", "value": {"negate": {"operand": {"numeric": {"text": "1"}}}}}}]),
            column("d", None, [{"default": {"sourceText": "CURRENT_TIMESTAMP",
                                            "value": {"currentTime": {"keyword": "CURRENT_TIMESTAMP"}}}}]),
            column("e", None, [{"default": {"sourceText": "'x''y'", "value": {"string": {"bytes": list(b"x'y")}}}}]),
            column("f", None)],
            "constraints": [{"primaryKey": {"columns": ["a"], "algorithm": None}},
                            {"unique": {"columns": ["c", "d"], "algorithm": None}}],
            "options": {"withoutRowid": False}}},
        {"createIndex": {"name": "i", "unique": True, "table": "Big T", "terms": [
            {"expression": {"identifier": {"name": "a", "quote": "none"}}, "descending": False},
            {"expression": {"identifier": {"name": "B", "quote": "none"}}, "descending": False}], "filter": None}},
        {"addColumn": {"table": "t", "column": column("z", "INT", [
            {"default": {"sourceText": "y", "value": {"identifier": {"name": "y", "quote": "none"}}}}])}}]


def test_collations_keep_their_names_as_written(parse_sql: Callable[..., Translation]) -> None:
    """`COLLATE` maps on a column, quoted or not, and as an expression, also in `ORDER BY` and
    an index term, with the name as written; resolution decides what the name means
    (ADR 0014, slice 3)."""
    sql = ("CREATE TABLE t(a TEXT COLLATE NoCase, b COLLATE 'rtrim');"
           "SELECT a COLLATE binary = b FROM t ORDER BY b COLLATE nocase DESC;"
           "CREATE INDEX i ON t(a COLLATE rtrim);")
    a, b = {"identifier": {"name": "a", "quote": "none"}}, {"identifier": {"name": "b", "quote": "none"}}
    table, query, index = mapped(parse_sql, sql)
    assert table["createTable"]["columns"] == [column("a", "TEXT", [{"collate": {"name": "NoCase"}}]),
                                               column("b", None, [{"collate": {"name": "rtrim"}}])]
    assert query["select"]["columns"][0]["expression"]["value"] == {
        "compare": {"operator": "eq", "left": {"collate": {"operand": a, "name": "binary"}}, "right": b}}
    assert query["select"]["orderBy"] == [{"expression": {"collate": {"operand": b, "name": "nocase"}},
                                           "descending": True}]
    assert index["createIndex"]["terms"] == [{"expression": {"collate": {"operand": a, "name": "rtrim"}},
                                              "descending": False}]


def test_writes_keep_rows_assignments_and_numeric_text(parse_sql: Callable[..., Translation]) -> None:
    """INSERT keeps its optional columns and rows, with no ON CONFLICT clauses; UPDATE keeps
    assignments and its filter."""
    sql = ("BEGIN DEFERRED TRANSACTION; INSERT INTO t VALUES (0x1F, \"q\"), (NULL, X'00ff'); "
           "INSERT INTO t(a) VALUES (+1_000); UPDATE t SET a = -2.5, b = 'é' WHERE id == 3; "
           "UPDATE t SET a = 1; END; ROLLBACK TRANSACTION;")
    assert mapped(parse_sql, sql) == [
        "begin",
        {"insert": {"table": "t", "columns": None, "rows": [
            [{"numeric": {"text": "0x1F"}}, {"identifier": {"name": "q", "quote": "double"}}],
            ["null", {"blob": {"bytes": [0, 255]}}]], "conflicts": [], "algorithm": None, "returning": []}},
        {"insert": {"table": "t", "columns": ["a"], "rows": [
            [{"positive": {"operand": {"numeric": {"text": "1_000"}}}}]], "conflicts": [], "algorithm": None,
            "returning": []}},
        {"update": {"table": "t", "assignments": [
            ["a", {"negate": {"operand": {"numeric": {"text": "2.5"}}}}],
            ["b", {"string": {"bytes": list("é".encode())}}]],
            "filter": {"compare": {"operator": "eq", "left": {"identifier": {"name": "id", "quote": "none"}},
                                  "right": {"numeric": {"text": "3"}}}}, "returning": []}},
        {"update": {"table": "t", "assignments": [["a", {"numeric": {"text": "1"}}]], "filter": None, "returning": []}},
        "commit", "rollback"]


@pytest.mark.parametrize(("sql", "refused"), [
    ("CREATE TEMP TABLE t(a);", "TEMP"), ("CREATE TABLE IF NOT EXISTS t(a);", "IF NOT EXISTS"),
    ("CREATE TABLE main.t(a);", ".t"), ("CREATE TABLE t(a) STRICTER;", "STRICTER"),
    ("CREATE TABLE t AS SELECT 1;", "AS SELECT 1"),
    ("CREATE TABLE t(a, UNIQUE(a COLLATE NOCASE));", "a COLLATE NOCASE"),
    ("CREATE TABLE t(a, FOREIGN KEY (a DESC) REFERENCES p);", "DESC"), ("CREATE TABLE t(a, PRIMARY KEY(a DESC));", "DESC"),
    ("CREATE TABLE t(a DEFAULT (1));", "DEFAULT (1)"),
    ("ALTER TABLE t RENAME TO u;", "ALTER TABLE t RENAME TO u"), ("BEGIN IMMEDIATE;", "IMMEDIATE"),
    ("UPDATE OR REPLACE t SET a = 1;", "OR REPLACE"), ("INSERT INTO t SELECT 1;", "SELECT 1"),
    ("INSERT INTO t VALUES (a & 1);", "a & 1"), ("UPDATE t SET a = 1 WHERE a IN u;", "a IN u"),
    ("UPDATE t SET (a, b) = (1, 2);", "(a, b) = (1, 2)"), ("EXPLAIN SELECT 1;", "EXPLAIN SELECT 1;"),
])
def test_syntax_without_a_constructor_is_unsupported_at_its_range(
        parse_sql: Callable[..., Translation], sql: str, refused: str) -> None:
    """Each refusal is UNSUPPORTED and its byte range is the refused syntax."""
    with pytest.raises(SqlError) as raised:
        parse_sql(sql).statements()
    assert raised.value.status == "UNSUPPORTED"
    assert sql.encode()[raised.value.start:raised.value.end].decode() == refused


@pytest.mark.parametrize(("sql", "advice"), [
    ("ALTER TABLE t RENAME TO u;", "rewrite it with the modeled forms: CREATE TABLE"),
    ("UPDATE t SET (a, b) = (1, 2);", "rewrite it with the modeled forms: CREATE TABLE"),
    ("INSERT INTO t SELECT 1;", "write INSERT ... VALUES (...)"),
    ("CREATE TABLE t(a DEFAULT (1));", "use NOT NULL, PRIMARY KEY, UNIQUE, COLLATE, CHECK, REFERENCES or DEFAULT with a literal"),
    ("VACUUM;", "the model runs CREATE TABLE"),
])
def test_refusals_say_which_form_to_use(parse_sql: Callable[..., Translation], sql: str, advice: str) -> None:
    """Refusals from `require`, `leftList`, `valueRows` and the dispatch (`Shapes.lean`, `Writes.lean`,
    `Statements.lean`) name the modeled forms."""
    with pytest.raises(SqlError) as raised:
        parse_sql(sql).statements()
    assert advice in str(raised.value)


@pytest.mark.parametrize("literal", ["X'00ff'", "x'00FF'", "- 7", "-7", '"true"', "[true]", "`true`", "'a''b'", "null"])
def test_default_source_spelling(parse_sql: Callable[..., Translation], literal: str) -> None:
    """Default syntax retains the text needed to predict SQLite catalog metadata."""
    statement = mapped(parse_sql, f"CREATE TABLE t(v BLOB DEFAULT {literal});")[0]
    constraint = statement["createTable"]["columns"][0]["constraints"][0]
    assert constraint["default"]["sourceText"] == literal

