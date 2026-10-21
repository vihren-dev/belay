"""Authored coverage cases of enforced foreign keys (ADR 0018, slice 4).

The cases follow the "Tests" list of the slice 4 task: the setting and the pragma inside a
transaction; a missing parent on `INSERT` and `UPDATE` of a child; each action on `DELETE` and
`UPDATE` of a parent, a chain of `CASCADE` and a table that references itself; `REPLACE` and
`DROP TABLE` of a parent; affinity and collation of the parent key; NULL child keys; composite
keys; foreign keys turned on over existing violations; the prepare errors of each write that
processes a foreign key, and the writes to the same tables that SQLite permits. Every case runs
under a measured profile with foreign keys on, which the recorder establishes before the setup.
Native SQLite is the only source of outcomes. The cases use `conformance.authored_queries.QueryCase`.
"""

from pathlib import Path
from tempfile import TemporaryDirectory

from conformance.authored_queries import QueryCase
from conformance.foreign_key_requirements import (
    PRAGMA, NO_TOGGLE, MISSING, NULL_KEY, SATISFIED, COMPOSITE_NULL,
    DEPENDENT, END_OF_STATEMENT, CASCADE, CASCADE_DELETE, CASCADE_UPDATE, SET_NULL,
    SET_DEFAULT, DEFAULT_MISSING, RESTRICT, RESTRICT_AT_ONCE, NO_ACTION, DEFAULT_ACTION,
    UPDATE_CHANGED, AFFINITY, COLLATION, IMPLICIT_DELETE, DROP_ACTIONS, DROP_FAILS,
    DROP_MISMATCH, MISMATCH_ERROR, MISMATCH_MESSAGE, MISMATCH_WRITES)
from conformance.case_format import Json
from conformance.execution_profile import ExecutionProfile, measured_profile
from conformance.native_connection import Connection, library_path, load_library
from conformance.native_record import record_sql

KEYS = ("CREATE TABLE p(id INTEGER PRIMARY KEY, k TEXT UNIQUE); "
        "CREATE TABLE c(x REFERENCES p(id) ON DELETE CASCADE, y REFERENCES p(k) ON DELETE SET NULL ON UPDATE CASCADE); "
        "INSERT INTO p VALUES(1, 'a'), (2, 'b'); INSERT INTO c VALUES(1, 'b'), (2, 'a');")
"""A parent with a rowid key and a TEXT key, and a child with one foreign key to each."""

ACTIONS = ("CREATE TABLE p(id PRIMARY KEY); INSERT INTO p VALUES(1), (2); "
           "CREATE TABLE cascade(x REFERENCES p ON DELETE CASCADE ON UPDATE CASCADE); "
           "CREATE TABLE nulls(x REFERENCES p ON DELETE SET NULL ON UPDATE SET NULL); "
           "CREATE TABLE defaults(x DEFAULT 2 REFERENCES p ON DELETE SET DEFAULT ON UPDATE SET DEFAULT); "
           "CREATE TABLE plain(x REFERENCES p); "
           "INSERT INTO cascade VALUES(1); INSERT INTO nulls VALUES(1); INSERT INTO defaults VALUES(1);")
"""A parent with a key that is no rowid, and a child for each action but RESTRICT."""

MISMATCH = ("CREATE TABLE p(a, b UNIQUE, v); CREATE TABLE c(x REFERENCES p(a), w); "
            "CREATE TABLE q(x REFERENCES missing, w);")
"""A child whose parent column has no unique index, and a child whose parent does not exist."""

def definitions() -> list[QueryCase]:
    """The coverage cases of enforced foreign keys."""
    case = QueryCase
    return [
        case("setting-pragma", "CREATE TABLE p(id PRIMARY KEY); CREATE TABLE c(x REFERENCES p);",
             "PRAGMA foreign_keys; BEGIN; PRAGMA foreign_keys = OFF; PRAGMA foreign_keys; INSERT INTO p VALUES(1); "
             "ROLLBACK; PRAGMA foreign_keys = 1; PRAGMA foreign_keys = yes; PRAGMA foreign_keys; INSERT INTO c VALUES(1);",
             (PRAGMA, NO_TOGGLE), ("pragma", "transaction")),
        case("child-insert", KEYS,
             "INSERT INTO c VALUES(NULL, NULL); INSERT INTO c VALUES(2, 'a') RETURNING x, y; SELECT * FROM c ORDER BY x, y; "
             "INSERT INTO c VALUES(1, 'c');",
             (MISSING, NULL_KEY, SATISFIED), ("child", "insert", "null")),
        case("child-insert-rows", KEYS, "INSERT INTO c VALUES(1, 'a'), (3, 'b');",
             (MISSING, END_OF_STATEMENT), ("child", "insert", "multi-row")),
        case("child-update", KEYS,
             "UPDATE c SET y = 'b' WHERE x = 2; UPDATE c SET x = NULL WHERE x = 1; SELECT * FROM c ORDER BY y; "
             "UPDATE c SET x = 9 WHERE x = 2;",
             (MISSING, NULL_KEY), ("child", "update")),
        case("parent-delete", KEYS, "DELETE FROM p WHERE id = 1; SELECT * FROM c ORDER BY x; SELECT * FROM p;",
             (CASCADE_DELETE, SET_NULL), ("parent", "delete", "cascade", "set-null")),
        case("parent-update", KEYS,
             "UPDATE p SET k = 'B' WHERE id = 2; SELECT * FROM c ORDER BY x; UPDATE p SET id = 5 WHERE id = 1;",
             (CASCADE_UPDATE, DEPENDENT, NO_ACTION), ("parent", "update", "cascade", "no-action")),
        case("delete-actions", ACTIONS,
             "DELETE FROM p WHERE id = 1; SELECT * FROM cascade; SELECT * FROM nulls; SELECT * FROM defaults; "
             "DELETE FROM p WHERE id = 2;",
             (CASCADE_DELETE, SET_NULL, SET_DEFAULT, DEFAULT_MISSING), ("delete", "cascade", "set-null", "set-default")),
        case("update-actions", ACTIONS,
             "UPDATE p SET id = 3 WHERE id = 1; SELECT * FROM cascade; SELECT * FROM nulls; SELECT * FROM defaults; "
             "SELECT * FROM p ORDER BY id;",
             (CASCADE_UPDATE, SET_NULL, SET_DEFAULT), ("update", "cascade", "set-null", "set-default")),
        case("update-unchanged", "CREATE TABLE p(k TEXT COLLATE NOCASE UNIQUE); "
             "CREATE TABLE c(x REFERENCES p(k) ON UPDATE CASCADE); INSERT INTO p VALUES('a'); INSERT INTO c VALUES('a');",
             "UPDATE p SET k = 'A'; SELECT * FROM c; SELECT * FROM p;",
             (UPDATE_CHANGED, COLLATION), ("update", "collation")),
        case("restrict-delete", "CREATE TABLE p(id PRIMARY KEY); CREATE TABLE c(x REFERENCES p ON DELETE RESTRICT); "
             "INSERT INTO p VALUES(1), (2); INSERT INTO c VALUES(1);",
             "DELETE FROM p WHERE id = 2; DELETE FROM p WHERE id = 1;",
             (RESTRICT, RESTRICT_AT_ONCE), ("restrict", "delete")),
        case("restrict-update", "CREATE TABLE p(id PRIMARY KEY); CREATE TABLE c(x REFERENCES p ON UPDATE RESTRICT); "
             "INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);",
             "UPDATE p SET id = 1 WHERE id = 1; UPDATE p SET id = 3 WHERE id = 1;",
             (RESTRICT, UPDATE_CHANGED), ("restrict", "update")),
        case("no-action-default", "CREATE TABLE p(id PRIMARY KEY); CREATE TABLE c(x REFERENCES p); "
             "INSERT INTO p VALUES(1), (2); INSERT INTO c VALUES(1);",
             "DELETE FROM p WHERE id = 2; SELECT * FROM p; DELETE FROM p WHERE id = 1;",
             (DEFAULT_ACTION, DEPENDENT), ("no-action", "delete")),
        case("cascade-chain", "CREATE TABLE a(id PRIMARY KEY); CREATE TABLE b(id PRIMARY KEY, a REFERENCES a ON DELETE CASCADE); "
             "CREATE TABLE c(b REFERENCES b ON DELETE CASCADE); INSERT INTO a VALUES(1), (2); "
             "INSERT INTO b VALUES(10, 1), (20, 2); INSERT INTO c VALUES(10), (20), (10);",
             "DELETE FROM a WHERE id = 1; SELECT * FROM b; SELECT * FROM c;",
             (CASCADE,), ("cascade", "chain")),
        case("self-reference", "CREATE TABLE t(id INTEGER PRIMARY KEY, p REFERENCES t ON DELETE CASCADE); "
             "INSERT INTO t VALUES(1, NULL), (2, 1), (3, 2), (4, NULL);",
             "INSERT INTO t VALUES(5, 5); INSERT INTO t VALUES(6, 7), (7, 4); DELETE FROM t WHERE id = 1; "
             "SELECT * FROM t ORDER BY id; INSERT INTO t VALUES(8, 9);",
             (CASCADE_DELETE, END_OF_STATEMENT), ("self-reference", "cascade", "multi-row")),
        case("replace-parent", "CREATE TABLE p(id INTEGER PRIMARY KEY, v); "
             "CREATE TABLE c(x REFERENCES p ON DELETE CASCADE); CREATE TABLE d(x REFERENCES p); "
             "INSERT INTO p VALUES(1, 'a'), (2, 'b'); INSERT INTO c VALUES(1); INSERT INTO d VALUES(2);",
             "INSERT OR REPLACE INTO p VALUES(1, 'c'); SELECT * FROM c; SELECT * FROM p ORDER BY id; "
             "INSERT OR REPLACE INTO p VALUES(2, 'd');",
             (CASCADE_DELETE, DEPENDENT), ("replace", "cascade")),
        case("drop-parent", "CREATE TABLE p(id PRIMARY KEY); CREATE TABLE q(id PRIMARY KEY); "
             "CREATE TABLE c(x REFERENCES p ON DELETE SET NULL); CREATE TABLE d(x REFERENCES q); "
             "INSERT INTO p VALUES(1); INSERT INTO q VALUES(1); INSERT INTO c VALUES(1); INSERT INTO d VALUES(1);",
             "DROP TABLE p; SELECT * FROM c; DROP TABLE q;",
             (IMPLICIT_DELETE, DROP_ACTIONS, DROP_FAILS), ("drop-table",)),
        case("drop-child-first", "CREATE TABLE q(id PRIMARY KEY); CREATE TABLE d(x REFERENCES q); "
             "INSERT INTO q VALUES(1); INSERT INTO d VALUES(1);",
             "DROP TABLE d; DROP TABLE q; CREATE TABLE q(id); SELECT * FROM q;",
             (IMPLICIT_DELETE,), ("drop-table",)),
        case("affinity", "CREATE TABLE p(id INTEGER PRIMARY KEY, n INTEGER UNIQUE, t TEXT UNIQUE); "
             "CREATE TABLE c(a REFERENCES p, b REFERENCES p(n), d INTEGER REFERENCES p(t)); "
             "INSERT INTO p VALUES(1, 2, '3'), (4, 5, '06');",
             "INSERT INTO c VALUES('1', NULL, NULL); INSERT INTO c VALUES(NULL, '2.0', NULL); INSERT INTO c VALUES(NULL, NULL, 3); "
             "SELECT a, typeof(a), b, d FROM c; INSERT INTO c VALUES(NULL, NULL, '06');",
             (AFFINITY,), ("affinity",)),
        case("affinity-rowid", "CREATE TABLE p(id INTEGER PRIMARY KEY); CREATE TABLE c(a REFERENCES p); INSERT INTO p VALUES(1);",
             "INSERT INTO c VALUES(1.0); INSERT INTO c VALUES('1'); INSERT INTO c VALUES('x');",
             (AFFINITY,), ("affinity", "rowid")),
        case("affinity-scan", "CREATE TABLE p(k TEXT UNIQUE); CREATE TABLE c(x INTEGER REFERENCES p(k)); "
             "INSERT INTO p VALUES('1'), ('01'); INSERT INTO c VALUES(1);",
             "DELETE FROM p WHERE k = '01';",
             (AFFINITY, END_OF_STATEMENT), ("affinity", "delete")),
        case("collation", "CREATE TABLE p(k TEXT COLLATE NOCASE PRIMARY KEY); CREATE TABLE c(x REFERENCES p); "
             "INSERT INTO p VALUES('Abc');",
             "INSERT INTO c VALUES('aBC'); SELECT * FROM c; DELETE FROM p;",
             (COLLATION,), ("collation",)),
        case("collation-missing", "CREATE TABLE p(k TEXT COLLATE NOCASE PRIMARY KEY); CREATE TABLE c(x REFERENCES p); "
             "INSERT INTO p VALUES('Abc');",
             "INSERT INTO c VALUES('abd');",
             (COLLATION, MISSING), ("collation",)),
        case("composite", "CREATE TABLE p(a TEXT COLLATE NOCASE, b INTEGER, UNIQUE(a, b)); "
             "CREATE TABLE c(x, y, FOREIGN KEY(y, x) REFERENCES p(b, a)); INSERT INTO p VALUES('A', 1);",
             "INSERT INTO c VALUES('a', '1'); INSERT INTO c VALUES('b', NULL); SELECT * FROM c ORDER BY x; "
             "INSERT INTO c VALUES('b', 1);",
             (COMPOSITE_NULL, AFFINITY, COLLATION), ("composite", "null")),
        case("old-violations", "PRAGMA foreign_keys = OFF; CREATE TABLE p(id INTEGER PRIMARY KEY); "
             "CREATE TABLE c(x REFERENCES p, v); INSERT INTO p VALUES(1); INSERT INTO c VALUES(1, 'a'), (9, 'b'), (8, 'c'); "
             "PRAGMA foreign_keys = ON;",
             "INSERT INTO c VALUES(NULL, 'd'); UPDATE c SET v = 'e' WHERE x = 9; UPDATE p SET id = 8 WHERE id = 1; "
             "SELECT * FROM p; SELECT * FROM c ORDER BY v; UPDATE c SET x = 7 WHERE x = 9;",
             (END_OF_STATEMENT,), ("existing-violations",)),
        case("fail-algorithm", "CREATE TABLE p(id PRIMARY KEY); CREATE TABLE c(x REFERENCES p, u UNIQUE);",
             "INSERT INTO c VALUES(NULL, 1); INSERT OR FAIL INTO c VALUES(5, 2), (NULL, 1);",
             (END_OF_STATEMENT,), ("fail", "multi-row")),
        case("mismatch-child-insert", MISMATCH, "INSERT INTO c VALUES(1, 'a');",
             (MISMATCH_ERROR, MISMATCH_MESSAGE, MISMATCH_WRITES), ("mismatch", "child")),
        case("mismatch-child-delete", MISMATCH, "UPDATE c SET w = 'b'; DELETE FROM c;",
             (MISMATCH_ERROR, MISMATCH_WRITES), ("mismatch", "child")),
        case("mismatch-child-update", MISMATCH, "UPDATE c SET x = 2;",
             (MISMATCH_ERROR, MISMATCH_WRITES), ("mismatch", "child")),
        case("mismatch-parent-insert", MISMATCH,
             "INSERT INTO p VALUES(1, 2, 3); UPDATE p SET v = 4; UPDATE p SET b = 5; INSERT INTO p VALUES(6, 7, 8), (9, 10, 11);",
             (MISMATCH_ERROR, MISMATCH_WRITES), ("mismatch", "parent")),
        case("mismatch-parent-delete", MISMATCH, "DELETE FROM p;", (MISMATCH_ERROR, MISMATCH_WRITES), ("mismatch", "parent")),
        case("mismatch-parent-update", MISMATCH, "UPDATE p SET a = 12;", (MISMATCH_ERROR, MISMATCH_WRITES),
             ("mismatch", "parent")),
        case("mismatch-replace", "CREATE TABLE p(id INTEGER PRIMARY KEY, v); CREATE TABLE r(a, v); "
             "CREATE TABLE c(x REFERENCES p(v)); CREATE TABLE d(x REFERENCES r(a));",
             "INSERT OR REPLACE INTO r VALUES(1, 2); INSERT OR REPLACE INTO p VALUES(1, 2);",
             (MISMATCH_ERROR, MISMATCH_WRITES), ("mismatch", "replace")),
        case("missing-parent-insert", MISMATCH, "UPDATE q SET w = 'a'; INSERT INTO q VALUES(NULL, 'b');",
             (MISMATCH_ERROR, MISMATCH_MESSAGE), ("mismatch", "missing-table")),
        case("missing-parent-delete", MISMATCH, "DELETE FROM q;", (MISMATCH_ERROR, MISMATCH_MESSAGE),
             ("mismatch", "missing-table")),
        case("drop-mismatch", "PRAGMA foreign_keys = OFF; CREATE TABLE p(a, b); CREATE TABLE c(x REFERENCES p(a)); "
             "INSERT INTO c VALUES(1); PRAGMA foreign_keys = ON;",
             "DROP TABLE p; SELECT * FROM c;",
             (DROP_MISMATCH,), ("drop-table", "mismatch")),
    ]


def profile() -> ExecutionProfile:
    """A measured profile of format 3 with SQLite's default settings, except that foreign keys
    are on."""
    with TemporaryDirectory(prefix="foreign-keys-profile-") as directory:
        connection = Connection(load_library(library_path()), Path(directory) / "measure.db")
        try:
            return measured_profile(connection, name="foreign-keys-v1", format_version=3, foreign_keys=True)
        finally:
            connection.close()


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs under the profile with foreign
    keys on, in the part `foreign-keys`, with its features."""
    selected = definitions() if cases is None else cases
    measured = profile()
    return [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements), outputs=True,
                          profile=measured),
             "part": "foreign-keys", "features": list(case.features)}
            for case in selected]
