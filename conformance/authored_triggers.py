"""Authored coverage cases of triggers (ADR 0018, slice 5).

The cases follow the "Tests" list of the slice 5 task: each time and event with `NEW` and `OLD`;
the order of two triggers; `UPDATE OF` with and without a listed column; `WHEN`; each `RAISE`
form in a `BEFORE` and an `AFTER` trigger, also on a later row of a multi-row write; `RAISE(IGNORE)`
over a row with a NULL in a NOT NULL column, and the checks that come before the `BEFORE`
triggers; a trigger that writes a table with its own trigger and one that would fire itself;
`REPLACE` with a `DELETE` trigger; a foreign-key action that fires a trigger; `DROP TABLE` and
`DROP TRIGGER`; the change count; the conflict algorithm that a body inherits; the collation and
affinity of `NEW` and `OLD`; and the prepare errors of the definitions, of a body that names a
missing table or `OLD` in an `INSERT` trigger, and of `RAISE` outside a trigger. The cases run
under the measured profile with foreign keys on of the foreign-key cases. Native SQLite is the
only source of outcomes. The cases use `conformance.authored_queries.QueryCase`.
"""

from conformance.authored_foreign_keys import profile
from conformance.authored_queries import QueryCase
from conformance.case_format import Json
from conformance.native_record import record_sql
from conformance.trigger_requirements import (
    CREATE, EVENTS, EACH_ROW, EACH_ROW_OPTIONAL, ROWS, RELEVANT_ROWS, TIME, BEFORE_DEFAULT, WHEN, NO_WHEN,
    OUTER_CONFLICT, BODY_CONFLICT, RAISE, RAISE_IGNORE, IGNORE_KEEPS, IGNORE_NESTED, RAISE_STOPS,
    REPLACE_NO_DELETE, ACTION_SEQUENCE, DROPPED_WITH_TABLE, DROP_TRIGGER, DROPPED_NOT_FIRED, SAME_NAME, CHANGES)

TABLES = ("CREATE TABLE t(id INTEGER PRIMARY KEY, v, w TEXT COLLATE NOCASE); "
          "CREATE TABLE log(n INTEGER PRIMARY KEY, x, y);")
"""A table with a rowid alias, an untyped column and a NOCASE column, and a log in written order."""

LOG = "SELECT n, x, y FROM log ORDER BY n;"
"""The log in the order that the triggers wrote it."""


def definitions() -> list[QueryCase]:
    """The coverage cases of triggers."""
    case = QueryCase
    return [
        case("insert-new", TABLES,
             "CREATE TRIGGER b BEFORE INSERT ON t BEGIN INSERT INTO log(x, y) VALUES ('before', new.id); END; "
             "CREATE TRIGGER a AFTER INSERT ON t FOR EACH ROW BEGIN INSERT INTO log(x, y) VALUES ('after', new.id); END; "
             "CREATE TRIGGER d INSERT ON t BEGIN INSERT INTO log(x, y) VALUES ('default', typeof(new.v)); END; "
             "INSERT INTO t(id, v) VALUES (NULL, '5'), (7, 8); " + LOG,
             (CREATE, EVENTS, EACH_ROW, EACH_ROW_OPTIONAL, ROWS, TIME, BEFORE_DEFAULT, NO_WHEN), ("insert", "new")),
        case("update-old-new", TABLES + " INSERT INTO t VALUES (1, 'a', 'x'), (2, 'b', 'y');",
             "CREATE TRIGGER b BEFORE UPDATE ON t BEGIN INSERT INTO log(x, y) VALUES (old.v, new.v); END; "
             "CREATE TRIGGER a AFTER UPDATE ON t BEGIN INSERT INTO log(x, y) VALUES (new.v, old.id); END; "
             "UPDATE t SET v = v || '!' WHERE id <= 2; " + LOG,
             (ROWS, TIME, EACH_ROW), ("update", "new", "old")),
        case("delete-old", TABLES + " INSERT INTO t VALUES (1, 'a', 'x'), (2, 'b', 'y');",
             "CREATE TRIGGER b BEFORE DELETE ON t BEGIN INSERT INTO log(x, y) VALUES ('before', old.v); END; "
             "CREATE TRIGGER a AFTER DELETE ON t BEGIN INSERT INTO log(x, y) VALUES ('after', old.v || old.w); END; "
             "DELETE FROM t; " + LOG,
             (ROWS, TIME, RELEVANT_ROWS), ("delete", "old")),
        case("order", TABLES,
             "CREATE TRIGGER a AFTER INSERT ON t BEGIN INSERT INTO log(x, y) VALUES ('a', new.id); END; "
             "CREATE TRIGGER b AFTER INSERT ON t BEGIN INSERT INTO log(x, y) VALUES ('b', new.id); END; "
             "CREATE TRIGGER c BEFORE INSERT ON t BEGIN INSERT INTO log(x, y) VALUES ('c', new.id); END; "
             "INSERT INTO t(v) VALUES (1), (2); " + LOG,
             (TIME, EACH_ROW), ("order",)),
        case("update-of", TABLES + " INSERT INTO t VALUES (1, 1, 'x');",
             "CREATE TRIGGER u AFTER UPDATE OF v, nosuch ON t BEGIN INSERT INTO log(x, y) VALUES (old.v, new.v); END; "
             "UPDATE t SET w = 'z'; UPDATE t SET id = 2; UPDATE t SET v = 5, w = 'q'; " + LOG,
             (EVENTS, ROWS), ("update-of",)),
        case("when", TABLES + " INSERT INTO t VALUES (1, NULL, 'x'), (2, 0, 'y'), (3, 4, 'z');",
             "CREATE TRIGGER d AFTER DELETE ON t WHEN old.v BEGIN INSERT INTO log(x) VALUES (old.id); END; "
             "DELETE FROM t; " + LOG,
             (WHEN, NO_WHEN), ("when", "null")),
        case("ignore-before", TABLES,
             "CREATE TRIGGER i BEFORE INSERT ON t WHEN new.v = 8 BEGIN SELECT RAISE(IGNORE); END; "
             "INSERT INTO t(v) VALUES (7), (8), (9); SELECT id, v FROM t ORDER BY id;",
             (RAISE, RAISE_IGNORE, IGNORE_KEEPS), ("raise", "ignore", "before")),
        case("ignore-after", TABLES,
             "CREATE TRIGGER a AFTER INSERT ON t BEGIN INSERT INTO log(x) VALUES (new.v); END; "
             "CREATE TRIGGER i AFTER INSERT ON t BEGIN SELECT RAISE(IGNORE) WHERE new.v = 9; END; "
             "INSERT INTO t(v) VALUES (1), (9), (3); SELECT id, v FROM t ORDER BY id; " + LOG,
             (RAISE_IGNORE, IGNORE_KEEPS), ("raise", "ignore", "after")),
        case("ignore-nested", TABLES + " CREATE TABLE u(a);",
             "CREATE TRIGGER i BEFORE INSERT ON u BEGIN SELECT RAISE(IGNORE) WHERE new.a = 2; END; "
             "CREATE TRIGGER a AFTER INSERT ON t BEGIN INSERT INTO u VALUES (new.v); INSERT INTO log(x) VALUES (new.v); END; "
             "INSERT INTO t(v) VALUES (1), (2); SELECT a FROM u; " + LOG,
             (RAISE_IGNORE, IGNORE_NESTED), ("raise", "ignore", "nested")),
        case("abort-before", TABLES + " INSERT INTO t VALUES (1, 0, 'x');",
             "CREATE TRIGGER f BEFORE INSERT ON t BEGIN SELECT RAISE(ABORT, 'no') WHERE new.v = 2; END; "
             "INSERT INTO t(v) VALUES (1), (2);",
             (RAISE, RAISE_STOPS), ("raise", "abort", "before")),
        case("abort-after", TABLES + " INSERT INTO t VALUES (1, 0, 'x');",
             "CREATE TRIGGER f AFTER UPDATE ON t BEGIN SELECT RAISE(ABORT, 'no'); END; UPDATE t SET v = 1;",
             (RAISE_STOPS,), ("raise", "abort", "after")),
        case("fail-later-row", TABLES,
             "CREATE TRIGGER f AFTER INSERT ON t BEGIN SELECT RAISE(FAIL, 'no') WHERE new.v = 2; END; "
             "INSERT INTO t(v) VALUES (1), (2), (3);",
             (RAISE_STOPS,), ("raise", "fail", "after", "multi-row")),
        case("fail-kept", TABLES,
             "CREATE TRIGGER f BEFORE INSERT ON t BEGIN SELECT RAISE(FAIL, 'no') WHERE new.v = 2; END; "
             "INSERT INTO log(x) VALUES (0); INSERT INTO t(v) VALUES (1), (2), (3);",
             (RAISE_STOPS,), ("raise", "fail", "before", "multi-row")),
        case("rollback", TABLES,
             "CREATE TRIGGER f AFTER INSERT ON t BEGIN SELECT RAISE(ROLLBACK, 'no'); END; "
             "BEGIN; INSERT INTO log(x) VALUES (1); INSERT INTO t(v) VALUES (1);",
             (RAISE_STOPS,), ("raise", "rollback", "transaction")),
        case("raise-case", TABLES,
             "CREATE TRIGGER f BEFORE INSERT ON t BEGIN SELECT CASE WHEN new.v = 1 THEN RAISE(ABORT, 'one') "
             "WHEN new.v = 2 THEN RAISE(IGNORE) ELSE 0 END; END; "
             "INSERT INTO t(v) VALUES (2), (3); SELECT v FROM t; INSERT INTO t(v) VALUES (1);",
             (RAISE, RAISE_IGNORE, RAISE_STOPS), ("raise", "case")),
        case("ignore-not-null", "CREATE TABLE n(a INTEGER NOT NULL);",
             "CREATE TRIGGER i BEFORE INSERT ON n BEGIN SELECT RAISE(IGNORE) WHERE new.a IS NULL; END; "
             "INSERT INTO n VALUES (NULL), (1); SELECT a FROM n;",
             (RAISE_IGNORE, TIME), ("raise", "ignore", "not-null")),
        case("strict-before-trigger", "CREATE TABLE s(a INTEGER) STRICT;",
             "CREATE TRIGGER i BEFORE INSERT ON s BEGIN SELECT RAISE(IGNORE); END; INSERT INTO s VALUES ('x');",
             (TIME,), ("raise", "strict")),
        case("alias-before-trigger", TABLES,
             "CREATE TRIGGER i BEFORE INSERT ON t BEGIN SELECT RAISE(IGNORE); END; INSERT INTO t(id) VALUES ('abc');",
             (TIME,), ("raise", "rowid-alias")),
        case("nested", TABLES + " CREATE TABLE u(a);",
             "CREATE TRIGGER a AFTER INSERT ON t BEGIN INSERT INTO u VALUES (new.v * 10); END; "
             "CREATE TRIGGER b AFTER INSERT ON u BEGIN INSERT INTO log(x) VALUES (new.a); END; "
             "INSERT INTO t(v) VALUES (1), (2); " + LOG,
             (EACH_ROW,), ("nested",)),
        case("not-recursive", TABLES + " INSERT INTO t VALUES (1, 100, 'x');",
             "CREATE TRIGGER u AFTER UPDATE ON t BEGIN UPDATE t SET v = v + 1 WHERE id = new.id; END; "
             "CREATE TRIGGER i AFTER INSERT ON t BEGIN INSERT INTO t(v) VALUES (new.v + 1); END; "
             "UPDATE t SET v = 100; INSERT INTO t(v) VALUES (5); SELECT id, v FROM t ORDER BY id;",
             (EACH_ROW,), ("recursion",)),
        case("replace", TABLES + " INSERT INTO t VALUES (1, 1, 'x');",
             "CREATE TRIGGER d AFTER DELETE ON t BEGIN INSERT INTO log(x) VALUES (old.v); END; "
             "CREATE TRIGGER i AFTER INSERT ON t BEGIN INSERT INTO log(x) VALUES (new.v); END; "
             "INSERT OR REPLACE INTO t VALUES (1, 2, 'y'); " + LOG,
             (REPLACE_NO_DELETE,), ("replace",)),
        case("action-fires", "CREATE TABLE p(id PRIMARY KEY); CREATE TABLE c(x REFERENCES p ON DELETE CASCADE); "
             "CREATE TABLE log(n INTEGER PRIMARY KEY, x, y); INSERT INTO p VALUES (1), (2); INSERT INTO c VALUES (1), (2);",
             "CREATE TRIGGER d AFTER DELETE ON c BEGIN INSERT INTO log(x) VALUES (old.x); END; "
             "CREATE TRIGGER b BEFORE DELETE ON p BEGIN INSERT INTO log(x) VALUES ('p' || old.id); END; "
             "DELETE FROM p WHERE id = 1; " + LOG,
             (ACTION_SEQUENCE,), ("foreign-keys", "cascade")),
        case("drop", TABLES,
             "CREATE TRIGGER t AFTER INSERT ON t BEGIN INSERT INTO log(x) VALUES (new.v); END; "
             "INSERT INTO t(v) VALUES (1); DROP TRIGGER t; INSERT INTO t(v) VALUES (2); "
             "CREATE TRIGGER r AFTER INSERT ON t BEGIN INSERT INTO log(x) VALUES (new.v); END; "
             "DROP TABLE t; CREATE TABLE t(id INTEGER PRIMARY KEY, v); INSERT INTO t(v) VALUES (3); "
             "DROP TRIGGER IF EXISTS r; " + LOG,
             (DROP_TRIGGER, DROPPED_NOT_FIRED, DROPPED_WITH_TABLE, SAME_NAME), ("drop",)),
        case("changes", TABLES,
             "CREATE TRIGGER a AFTER INSERT ON t BEGIN INSERT INTO log(x) VALUES (1); INSERT INTO log(x) VALUES (2); END; "
             "INSERT INTO t(v) VALUES (1), (2) RETURNING id;",
             (CHANGES,), ("changes",)),
        case("inherited-conflict", TABLES + " CREATE TABLE u(a UNIQUE); INSERT INTO u VALUES (1);",
             "CREATE TRIGGER a AFTER INSERT ON t BEGIN INSERT INTO u VALUES (new.v); "
             "INSERT OR IGNORE INTO log(n, x) VALUES (1, new.v); END; "
             "INSERT INTO log(n, x) VALUES (1, 0); INSERT OR IGNORE INTO t(v) VALUES (1); SELECT a FROM u; " + LOG +
             " INSERT INTO t(v) VALUES (1);",
             (OUTER_CONFLICT, BODY_CONFLICT), ("conflict",)),
        case("row-collation", TABLES,
             "CREATE TRIGGER a AFTER INSERT ON t BEGIN INSERT INTO log(x, y) VALUES (new.w = 'X', new.v = '5'); END; "
             "INSERT INTO t(v, w) VALUES (5, 'x'); " + LOG,
             (ROWS,), ("collation", "affinity")),
        case("missing-table", TABLES,
             "CREATE TRIGGER a AFTER DELETE ON t BEGIN INSERT INTO nosuch VALUES (1); END; "
             "INSERT INTO t(v) VALUES (1); DELETE FROM t WHERE id = 99;",
             (CREATE,), ("prepare-error", "body")),
        case("old-in-insert", TABLES,
             "CREATE TRIGGER a AFTER INSERT ON t BEGIN INSERT INTO log(x) VALUES (old.v); END; INSERT INTO t(v) VALUES (1);",
             (RELEVANT_ROWS,), ("prepare-error", "old")),
        case("trigger-exists", TABLES,
             "CREATE TRIGGER a AFTER INSERT ON t BEGIN SELECT 1; END; "
             "CREATE TRIGGER IF NOT EXISTS a AFTER DELETE ON t BEGIN SELECT 1; END; "
             "CREATE TRIGGER a AFTER DELETE ON t BEGIN SELECT 1; END;",
             (CREATE,), ("prepare-error", "definition")),
        case("no-such-trigger", TABLES, "DROP TRIGGER IF EXISTS a; DROP TRIGGER a;",
             (DROP_TRIGGER,), ("prepare-error", "drop")),
        case("system-table", TABLES,
             "CREATE TRIGGER a AFTER INSERT ON sqlite_master BEGIN SELECT 1; END;",
             (CREATE,), ("prepare-error", "definition")),
        case("trigger-table-missing", TABLES,
             "CREATE TRIGGER a AFTER INSERT ON nosuch BEGIN SELECT 1; END;",
             (CREATE,), ("prepare-error", "definition")),
        case("raise-outside", TABLES, "SELECT RAISE(IGNORE);",
             (RAISE,), ("prepare-error", "raise")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs under the profile with foreign
    keys on of `conformance.authored_foreign_keys`, which the case of an action needs and the other
    cases do not read, in the part `triggers`, with its features."""
    selected = definitions() if cases is None else cases
    measured = profile()
    return [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements), outputs=True,
                          profile=measured),
             "part": "triggers", "features": list(case.features)}
            for case in selected]
