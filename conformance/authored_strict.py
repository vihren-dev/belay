"""Authored coverage cases of `STRICT` tables (ADR 0014, slice 6).

The cases follow the "Tests" list of the slice 6 task: each type with a value that fits
after its affinity and one that does not; `ANY` without affinity; NULL; the order NOT NULL,
type, CHECK; each conflict algorithm; UPDATE, `DO UPDATE` and a generated column; `STRICT,
WITHOUT ROWID`; and SQLite's prepare errors. Native SQLite is the only source of outcomes.
The cases use `conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE s(i INTEGER, n INT, r REAL, t TEXT, b BLOB, a ANY) STRICT; "
          "CREATE TABLE c(k INTEGER NOT NULL ON CONFLICT IGNORE, v INTEGER CHECK (v > 0), "
          "u INT UNIQUE ON CONFLICT REPLACE) STRICT; "
          "CREATE TABLE w(k TEXT PRIMARY KEY, v int) STRICT, WITHOUT ROWID; "
          "CREATE TABLE g(a INTEGER, b INTEGER AS (a + 0.5)) STRICT; "
          "INSERT INTO s VALUES(1, 2, 3.5, 'x', x'00', 'y'); INSERT INTO c VALUES(1, 1, 1);")
"""A STRICT table with each of the six types; one with NOT NULL under IGNORE, a CHECK and a
UNIQUE key under REPLACE; a STRICT WITHOUT ROWID table; and one whose generated column can
give a REAL value."""

STRICT = "R-62842-02885"
"""SQLite: with the STRICT table option, strict typing rules apply to the table."""
TYPES = "R-45202-42857"
"""SQLite: the datatype must be one of INT, INTEGER, REAL, TEXT, BLOB, ANY."""
DATATYPE_REQUIRED = "R-60210-08703"
"""SQLite: every column definition must specify a datatype."""
CONVERSION = "R-34136-00089"
"""SQLite: SQLite attempts to coerce the data into the column's type by the affinity rules."""
CONSTRAINT = "R-64842-30903"
"""SQLite: a value that cannot be losslessly converted is SQLITE_CONSTRAINT_DATATYPE."""
FITS = "R-43870-25292"
"""SQLite: a value in a column other than ANY must be NULL or the declared type."""
ANY = "R-01879-24612"
"""SQLite: an ANY column accepts any kind of data, and no type coercion occurs."""


def definitions() -> list[QueryCase]:
    """The coverage cases of STRICT tables."""
    case = QueryCase
    return [
        case("strict-values", TABLES, "SELECT i, n, r, t, b, a FROM s;", (STRICT, TYPES), ("strict", "select")),
        case("strict-coercion", TABLES,
             "INSERT INTO s VALUES(' 7 ', 8.0, 4, 5, NULL, '6'); SELECT i, n, r, t, b, a FROM s;", (CONVERSION, ANY),
             ("strict", "affinity")),
        case("strict-integer-text", TABLES, "INSERT INTO s(i) VALUES('abc');", (CONVERSION, CONSTRAINT),
             ("strict", "constraint")),
        case("strict-integer-real", TABLES, "INSERT INTO s(n) VALUES(1.5);", (CONVERSION, CONSTRAINT),
             ("strict", "constraint")),
        case("strict-real-blob", TABLES, "INSERT INTO s(r) VALUES(x'01');", (FITS,), ("strict", "constraint")),
        case("strict-text-blob", TABLES, "INSERT INTO s(t) VALUES(x'01');", (FITS,), ("strict", "constraint")),
        case("strict-blob-integer", TABLES, "INSERT INTO s(b) VALUES(1);", (FITS,), ("strict", "constraint")),
        case("strict-any", TABLES, "INSERT INTO s(a) VALUES(1), ('1'), (1.5), (x'02'); SELECT a FROM s;", (ANY,),
             ("strict", "any")),
        case("strict-nulls", TABLES, "INSERT INTO s VALUES(NULL, NULL, NULL, NULL, NULL, NULL); SELECT i FROM s;",
             (FITS,), ("strict", "null")),
        case("strict-after-not-null", TABLES, "INSERT INTO c VALUES(NULL, 'x', 2); SELECT k, v, u FROM c;",
             (CONVERSION,), ("strict", "not-null", "order")),
        case("strict-before-check", TABLES, "INSERT INTO c VALUES(2, 'x', 2);", (CONVERSION,),
             ("strict", "check", "order")),
        case("strict-or-ignore", TABLES, "INSERT OR IGNORE INTO s(i) VALUES('abc');", (CONSTRAINT,),
             ("strict", "or-ignore")),
        case("strict-or-replace", TABLES, "INSERT INTO c VALUES(2, 2, 1), (3, 3, 'q');", (CONSTRAINT,),
             ("strict", "or-replace")),
        case("strict-or-fail", TABLES, "INSERT OR FAIL INTO s(i) VALUES(5), ('q'); SELECT i FROM s;", (CONSTRAINT,),
             ("strict", "or-fail")),
        case("strict-or-rollback", TABLES,
             "BEGIN; INSERT INTO s(i) VALUES(5); INSERT OR ROLLBACK INTO s(i) VALUES('q'); SELECT i FROM s;",
             (CONSTRAINT,), ("strict", "or-rollback", "transaction")),
        case("strict-update", TABLES, "UPDATE s SET t = x'03';", (CONVERSION,), ("strict", "update")),
        case("strict-do-update", TABLES, "INSERT INTO c VALUES(5, 5, 1) ON CONFLICT(u) DO UPDATE SET v = 'q';",
             (CONVERSION,), ("strict", "on-conflict")),
        case("strict-generated", TABLES, "INSERT INTO g VALUES(1);", (CONVERSION,), ("strict", "generated")),
        case("strict-without-rowid", TABLES, "INSERT INTO w VALUES(1, '2'); SELECT k, v FROM w;", (CONVERSION,),
             ("strict", "without-rowid")),
        case("strict-unknown-type", TABLES, "CREATE TABLE n(a VARCHAR(10)) STRICT;", (TYPES,),
             ("strict", "prepare-error")),
        case("strict-missing-type", TABLES, "CREATE TABLE n(a, b INTEGER) STRICT;", (DATATYPE_REQUIRED,),
             ("strict", "prepare-error")),
        case("strict-create-runs", TABLES, "CREATE TABLE n(a text, b AnY) STRICT; INSERT INTO n VALUES(1, '2'); "
             "SELECT a, b FROM n;", (TYPES, ANY), ("strict", "create-table-runs")),
        case("strict-any-default", TABLES, "CREATE TABLE d(k INTEGER, a ANY DEFAULT '7', r REAL DEFAULT 2) STRICT; "
             "INSERT INTO d(k) VALUES(1); SELECT k, a, r FROM d;", (ANY,), ("strict", "any", "default")),
        case("strict-add-column-any", TABLES, "ALTER TABLE s ADD COLUMN z ANY DEFAULT '7'; SELECT i, z FROM s;",
             (ANY,), ("strict", "add-column", "any")),
        case("strict-add-column", TABLES, "ALTER TABLE s ADD COLUMN z REAL DEFAULT 1; SELECT i, z FROM s;", (TYPES,),
             ("strict", "add-column")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `strict`."""
    return query_records(definitions() if cases is None else cases, part="strict")
