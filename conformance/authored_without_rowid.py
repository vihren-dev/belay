"""Authored coverage cases of `WITHOUT ROWID` tables (ADR 0014, slice 2).

The cases follow the "Tests" list of the slice 2 task: the scan order of a text key, a
composite key and a descending key; a NULL key; an `INTEGER PRIMARY KEY` that is no rowid
alias; `rowid` as `no such column`; a table without a primary key; and INSERT, UPDATE,
DELETE, UPSERT, REPLACE and an index on such tables, with `RETURNING` in scan order.
Native SQLite is the only source of outcomes. The cases use
`conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE w(k TEXT PRIMARY KEY, v INTEGER) WITHOUT ROWID; "
          "CREATE TABLE c(a INTEGER, b TEXT, PRIMARY KEY(b, a)) WITHOUT ROWID; "
          "CREATE TABLE d(a INTEGER PRIMARY KEY DESC, b INTEGER) WITHOUT ROWID; "
          "CREATE TABLE x(a INTEGER PRIMARY KEY, b INTEGER) WITHOUT ROWID; "
          "INSERT INTO w VALUES('b', 1), ('a', 2); INSERT INTO c VALUES(2, 'b'), (1, 'b'), (3, 'a'); "
          "INSERT INTO d VALUES(1, 1), (3, 3), (2, 2);")
"""Tables with a text key, a composite key in another order than the columns, a descending
key and an `INTEGER PRIMARY KEY`, with rows inserted out of key order."""

WITHOUT_ROWID = "R-32341-39358"
"""SQLite: with WITHOUT ROWID the special rowid column is omitted."""
KEY_STORAGE = "R-26480-31567"
"""SQLite: each entry of the b-tree is keyed by the columns of the primary key."""
NOT_NULL = "R-27831-00579"
"""SQLite: NOT NULL is enforced on every column of the primary key of a WITHOUT ROWID table."""
NO_ALIAS = "R-09413-51939"
"""SQLite: the special behaviors of INTEGER PRIMARY KEY do not apply on WITHOUT ROWID tables."""
NO_ROWID_NAMES = "R-07387-29430"
"""SQLite: rowid, oid and _rowid_ are not available on WITHOUT ROWID tables."""
KEY_REQUIRED = "R-58033-17334"
"""SQLite: CREATE TABLE ... WITHOUT ROWID without a primary key is an error."""


def definitions() -> list[QueryCase]:
    """The coverage cases of `WITHOUT ROWID` tables."""
    case = QueryCase
    return [
        case("without-rowid-scan-text", TABLES, "SELECT k, v FROM w;", (KEY_STORAGE,), ("without-rowid", "scan")),
        case("without-rowid-scan-composite", TABLES, "SELECT a, b FROM c;", (KEY_STORAGE,),
             ("without-rowid", "scan", "composite")),
        case("without-rowid-scan-descending", TABLES, "SELECT a, b FROM d;", (KEY_STORAGE,),
             ("without-rowid", "scan", "descending")),
        case("without-rowid-insert-order", TABLES, "INSERT INTO w VALUES('c', 3), ('0', 4); SELECT k FROM w;",
             (KEY_STORAGE,), ("without-rowid", "insert", "scan")),
        case("without-rowid-null-key", TABLES, "INSERT INTO w VALUES(NULL, 3);", (NOT_NULL,),
             ("without-rowid", "not-null", "constraint")),
        case("without-rowid-integer-key-null", TABLES, "INSERT INTO x VALUES(NULL, 1);", (NOT_NULL, NO_ALIAS),
             ("without-rowid", "not-null", "constraint")),
        case("without-rowid-integer-key", TABLES, "INSERT INTO x VALUES(5, 1), (-2, 2); SELECT a, b FROM x;",
             (NO_ALIAS,), ("without-rowid", "integer-key")),
        case("without-rowid-duplicate-key", TABLES, "INSERT INTO w VALUES('a', 3);", (KEY_STORAGE,),
             ("without-rowid", "key", "constraint")),
        case("without-rowid-select-rowid", TABLES, "SELECT rowid FROM w;", (NO_ROWID_NAMES, WITHOUT_ROWID),
             ("without-rowid", "rowid", "prepare-error")),
        case("without-rowid-update-rowid", TABLES, "UPDATE w SET v = 9 WHERE oid = 1;", (NO_ROWID_NAMES,),
             ("without-rowid", "rowid", "prepare-error")),
        case("without-rowid-missing-key", TABLES, "CREATE TABLE n(a INTEGER) WITHOUT ROWID;", (KEY_REQUIRED,),
             ("without-rowid", "prepare-error")),
        case("without-rowid-update-returning", TABLES, "UPDATE w SET v = v + 10 RETURNING k, v;", (KEY_STORAGE,),
             ("without-rowid", "update", "returning")),
        case("without-rowid-update-key", TABLES, "UPDATE w SET k = 'z' WHERE k = 'a'; SELECT k, v FROM w;",
             (KEY_STORAGE,), ("without-rowid", "update", "key")),
        case("without-rowid-delete-returning", TABLES, "DELETE FROM c WHERE a > 1 RETURNING a, b;", (KEY_STORAGE,),
             ("without-rowid", "delete", "returning")),
        case("without-rowid-upsert", TABLES,
             "INSERT INTO w VALUES('a', 5) ON CONFLICT(k) DO UPDATE SET v = excluded.v; SELECT k, v FROM w;",
             (KEY_STORAGE,), ("without-rowid", "on-conflict")),
        case("without-rowid-replace", TABLES, "INSERT OR REPLACE INTO w VALUES('b', 7); SELECT k, v FROM w;",
             (KEY_STORAGE,), ("without-rowid", "replace")),
        case("without-rowid-index", TABLES, "CREATE UNIQUE INDEX wv ON w(v); INSERT INTO w VALUES('c', 1);",
             (KEY_STORAGE,), ("without-rowid", "index", "constraint")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `without-rowid`."""
    return query_records(definitions() if cases is None else cases, part="without-rowid")
