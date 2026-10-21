"""The mapping of CREATE TRIGGER, DROP TRIGGER and RAISE to Syntax JSON (`belay.sqlite.syntax_triggers`).

ADR 0018, D5: the frontend keeps a trigger's name, time, event, table, `WHEN` condition and
body statements, each body statement with every field of `Syntax.BodyStatement`, maps `RAISE`
as an expression, and refuses the forms that the model does not describe.
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


def column(name: str) -> dict[str, object]:
    """The JSON of an unquoted column name."""
    return {"identifier": {"name": name, "quote": "none"}}


def qualified(source: str, name: str) -> dict[str, object]:
    """The JSON of `source.name`."""
    return {"qualified": {"source": source, "column": name}}


def test_trigger_keeps_time_event_condition_and_body(parse_sql: Callable[..., Tree]) -> None:
    """`create_trigger` maps each part of the trigger, and every field of each body statement,
    the subqueries of each statement in its own list."""
    sql = ("CREATE TRIGGER IF NOT EXISTS r AFTER UPDATE OF a, b ON t FOR EACH ROW WHEN new.a > 1 BEGIN "
           "INSERT OR IGNORE INTO log(x) VALUES ((SELECT 1)); UPDATE log SET x = old.a WHERE x = 2; DELETE FROM log; "
           "SELECT RAISE(IGNORE) WHERE new.b; END;")
    [statement] = mapped(parse_sql, sql)
    trigger = statement["createTrigger"]
    assert {key: trigger[key] for key in ("name", "ifNotExists", "time", "event", "table")} == {
        "name": "r", "ifNotExists": True, "time": "after", "event": {"update": {"columns": ["a", "b"]}}, "table": "t"}
    assert trigger["condition"] == {"compare": {"operator": "gt", "left": qualified("new", "a"),
                                                "right": {"numeric": {"text": "1"}}}}
    insert, update, delete, select = trigger["body"]
    assert insert["insert"]["algorithm"] == "ignore" and insert["insert"]["columns"] == ["x"]
    assert insert["insert"]["rows"] == [[{"subquery": {"index": 0}}]] and len(insert["insert"]["subqueries"]) == 1
    assert update == {"update": {"table": "log", "assignments": [["x", qualified("old", "a")]],
                                 "filter": {"compare": {"operator": "eq", "left": column("x"),
                                                        "right": {"numeric": {"text": "2"}}}},
                                 "subqueries": []}}
    assert delete == {"delete": {"table": "log", "filter": None, "subqueries": []}}
    assert select["select"]["columns"][0]["expression"]["value"] == {"raise": {"kind": "ignore", "message": None}}
    assert select["select"]["having"] is None and select["select"]["distinct"] is False


def test_trigger_defaults_and_drop(parse_sql: Callable[..., Tree]) -> None:
    """A trigger without a time is BEFORE, `UPDATE` without OF has no columns, and DROP TRIGGER
    keeps `IF EXISTS`; RAISE keeps its kind and message."""
    sql = ("CREATE TRIGGER r UPDATE ON t BEGIN SELECT RAISE(FAIL, 'no'); END; DROP TRIGGER r; DROP TRIGGER IF EXISTS r;")
    create, drop, drop_if = mapped(parse_sql, sql)
    trigger = create["createTrigger"]
    assert (trigger["time"], trigger["event"], trigger["condition"]) == ("before", {"update": {"columns": []}}, None)
    assert trigger["body"][0]["select"]["columns"][0]["expression"]["value"] == {
        "raise": {"kind": "fail", "message": {"string": {"bytes": list(b"no")}}}}
    assert (drop, drop_if) == ({"dropTrigger": {"name": "r", "ifExists": False}},
                               {"dropTrigger": {"name": "r", "ifExists": True}})


@pytest.mark.parametrize(("sql", "message"), [
    ("CREATE TEMP TRIGGER r AFTER INSERT ON t BEGIN SELECT 1; END;", "A TEMP trigger"),
    ("CREATE TRIGGER r INSTEAD OF INSERT ON t BEGIN SELECT 1; END;", "INSTEAD OF triggers are not modeled"),
    ("CREATE TRIGGER main.r AFTER INSERT ON t BEGIN SELECT 1; END;", "A schema name"),
    ("CREATE TRIGGER r AFTER INSERT ON t WHEN EXISTS (SELECT 1) BEGIN SELECT 1; END;", "WHEN condition"),
    ("CREATE TRIGGER r AFTER INSERT ON t BEGIN UPDATE OR IGNORE t SET a = 1; END;", "An OR conflict clause"),
    ("CREATE TRIGGER r AFTER INSERT ON t BEGIN DELETE FROM t INDEXED BY i; END;", "INDEXED BY"),
    ("CREATE TRIGGER r AFTER INSERT ON t BEGIN INSERT INTO t SELECT 1; END;", "Only VALUES rows"),
    ("CREATE TRIGGER r AFTER INSERT ON t BEGIN INSERT INTO t VALUES (1) RETURNING a; END;", "RETURNING"),
])
def test_unmodeled_trigger_forms_are_refused(parse_sql: Callable[..., Tree], sql: str, message: str) -> None:
    """`create_trigger` refuses TEMP, INSTEAD OF, a schema name, a subquery in WHEN, UPDATE OR,
    INDEXED BY, INSERT ... SELECT and RETURNING with their source range."""
    with pytest.raises(SqlError) as raised:
        statements(parse_sql(sql))
    assert raised.value.status == "UNSUPPORTED" and message in str(raised.value)
