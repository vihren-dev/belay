"""Authored coverage cases of generated columns (ADR 0014, slice 5).

The cases follow the "Tests" list of the slice 5 task: both kinds and their `hidden` value;
a generated column that reads another and the rowid alias; the affinity of a generated
value; INSERT with and without a column list; UPDATE of a column that a generated column
reads; a UNIQUE, a NOT NULL, a CHECK and an index on a generated column; and SQLite's
prepare errors. A time keyword in a generated column is covered by Lean examples only: the
recorder refuses it outside a controlled clock. Native SQLite is the only source of outcomes. The cases use
`conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE g(a INTEGER, b INTEGER GENERATED ALWAYS AS (a * 2) STORED, c AS (b + 1), "
          "d TEXT AS (a + 0) VIRTUAL); "
          "CREATE TABLE k(id INTEGER PRIMARY KEY, v INTEGER, w AS (id * 10 + v) UNIQUE, "
          "x AS (v) NOT NULL, y AS (v - 1) CHECK (y >= 0)); "
          "INSERT INTO g(a) VALUES(1), (2); INSERT INTO k(v) VALUES(1);")
"""A table with a STORED and two VIRTUAL generated columns, one reading another and one
with TEXT affinity; a table whose generated columns read the rowid alias and carry UNIQUE,
NOT NULL and CHECK."""

READS_OTHERS = "R-22464-05974"
"""SQLite: a generated column may read the other columns, also generated ones, without a loop."""
DATATYPE = "R-14902-14650"
"""SQLite: generated columns can have a datatype."""
CONSTRAINTS = "R-44743-26048"
"""SQLite: generated columns may have NOT NULL, CHECK and UNIQUE constraints."""
NO_PRIMARY_KEY = "R-43641-06233"
"""SQLite: generated columns may not be part of the PRIMARY KEY."""
NO_DEFAULT = "R-44118-24115"
"""SQLite: generated columns may not have a default value."""
NO_ROWID = "R-39225-16568"
"""SQLite: a generated column may not reference the ROWID, but may reference the INTEGER PRIMARY KEY."""
NON_GENERATED = "R-31195-28735"
"""SQLite: every table must have at least one non-generated column."""
INDEXES = "R-63827-58581"
"""SQLite: generated columns can participate in indexes."""
ANYWHERE = "R-59999-34429"
"""SQLite: generated columns can be interspersed among ordinary columns."""


def definitions() -> list[QueryCase]:
    """The coverage cases of generated columns."""
    case = QueryCase
    return [
        case("generated-values", TABLES, "SELECT a, b, c, d FROM g;", (READS_OTHERS, DATATYPE),
             ("generated", "select")),
        case("generated-star", TABLES, "SELECT * FROM g WHERE c = 5;", (READS_OTHERS,), ("generated", "star")),
        case("generated-insert-columns", TABLES, "INSERT INTO g(a) VALUES(5); SELECT a, b, c FROM g;",
             (READS_OTHERS,), ("generated", "insert")),
        case("generated-insert-without-columns", TABLES, "INSERT INTO g VALUES(7); SELECT a, b, c, d FROM g;",
             (ANYWHERE,), ("generated", "insert")),
        case("generated-insert-count", TABLES, "INSERT INTO g VALUES(7, 14);", (ANYWHERE,),
             ("generated", "insert", "prepare-error")),
        case("generated-insert-named", TABLES, "INSERT INTO g(a, b) VALUES(7, 14);", (READS_OTHERS,),
             ("generated", "insert", "prepare-error")),
        case("generated-update", TABLES, "UPDATE g SET a = a + 10; SELECT a, b, c, d FROM g;", (READS_OTHERS,),
             ("generated", "update")),
        case("generated-update-named", TABLES, "UPDATE g SET c = 1;", (READS_OTHERS,),
             ("generated", "update", "prepare-error")),
        case("generated-returning", TABLES, "INSERT INTO g(a) VALUES(3) RETURNING b, c, d;", (READS_OTHERS,),
             ("generated", "returning")),
        case("generated-rowid-alias", TABLES, "INSERT INTO k(v) VALUES(2); SELECT id, w, x, y FROM k;",
             (NO_ROWID,), ("generated", "rowid-alias")),
        case("generated-unique", TABLES, "INSERT INTO k(id, v) VALUES(0, 11);", (CONSTRAINTS,),
             ("generated", "unique", "constraint")),
        case("generated-not-null", TABLES, "INSERT INTO k(v) VALUES(NULL);", (CONSTRAINTS,),
             ("generated", "not-null", "constraint")),
        case("generated-check", TABLES, "INSERT INTO k(v) VALUES(0);", (CONSTRAINTS,),
             ("generated", "check", "constraint")),
        case("generated-index", TABLES,
             "CREATE UNIQUE INDEX gi ON g(b); INSERT INTO g(a) VALUES(1);", (INDEXES,),
             ("generated", "index", "constraint")),
        case("generated-create-runs", TABLES,
             "CREATE TABLE n(a, b AS (a * 3)); INSERT INTO n VALUES(2); SELECT a, b FROM n;", (READS_OTHERS,),
             ("generated", "create-table-runs")),
        case("generated-primary-key", TABLES, "CREATE TABLE n(a, b AS (a) PRIMARY KEY);", (NO_PRIMARY_KEY,),
             ("generated", "prepare-error")),
        case("generated-table-primary-key", TABLES, "CREATE TABLE n(a, b AS (a), PRIMARY KEY (b));",
             (NO_PRIMARY_KEY,), ("generated", "prepare-error")),
        case("generated-default", TABLES, "CREATE TABLE n(a, b AS (a) DEFAULT 1);", (NO_DEFAULT,),
             ("generated", "prepare-error")),
        case("generated-rowid", TABLES, "CREATE TABLE n(a, b AS (rowid));", (NO_ROWID,),
             ("generated", "prepare-error")),
        case("generated-only", TABLES, "CREATE TABLE n(a AS (1));", (NON_GENERATED,),
             ("generated", "prepare-error")),
        case("generated-no-such-column", TABLES, "CREATE TABLE n(a, b AS (zz));", (READS_OTHERS,),
             ("generated", "prepare-error")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `generated`."""
    return query_records(definitions() if cases is None else cases, part="generated")
