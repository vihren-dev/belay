"""Authored coverage cases of CHECK constraints and foreign keys (ADR 0014, slice 4).

The cases follow the "Tests" list of the slice 4 task: a CHECK that fails, NULL that
passes and the numeric reading of the condition; the order NOT NULL, CHECK, unique keys;
each conflict algorithm; UPDATE and `DO UPDATE`; ADD COLUMN over rows and over an empty
table; CREATE TABLE with constraints that runs; foreign keys that SQLite does not enforce
and their prepare errors; and the prepare errors of a CHECK. Native SQLite is the only
source of outcomes. The cases use `conformance.authored_queries.QueryCase` and its
recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE k(a INTEGER CHECK (a > 0), b INTEGER NOT NULL ON CONFLICT IGNORE, CHECK (a != 5)); "
          "CREATE TABLE u(k INTEGER UNIQUE ON CONFLICT IGNORE, v INTEGER CHECK (v < 9)); "
          "CREATE TABLE c(a INTEGER CHECK (a > 0), t TEXT CONSTRAINT good CHECK (t <> 'bad')); "
          "CREATE TABLE p(a INTEGER); "
          "CREATE TABLE r(a REFERENCES nothere(x) ON DELETE CASCADE, b, FOREIGN KEY (b) REFERENCES k(a)); "
          "INSERT INTO k VALUES(1, 1); INSERT INTO u VALUES(1, 1); INSERT INTO c VALUES(2, 'ab'); "
          "INSERT INTO p VALUES(1);")
"""A table with a column and a table CHECK and a NOT NULL with IGNORE; a table with a UNIQUE
key with IGNORE and a CHECK; a table with a named CHECK; a table without constraints; and a
table with foreign keys, one to a missing table. Each has one row."""

FAILS = "R-55435-14303"
"""SQLite: a CHECK expression is cast to NUMERIC, and zero is a constraint violation."""
NULL_PASSES = "R-34109-39108"
"""SQLite: a CHECK that evaluates to NULL or any other non-zero value is no violation."""
EITHER_PLACE = "R-45493-35653"
"""SQLite: a CHECK may be a column or a table constraint, with no difference."""
REPLACE_ABORTS = "R-26383-51744"
"""SQLite: REPLACE works like ABORT for a CHECK violation."""
TABLE_CONFLICT = "R-29031-55583"
"""SQLite: the conflict clause of a table CHECK has no effect."""
IGNORE = "R-50299-05307"
"""SQLite: IGNORE skips the row that violates the constraint."""
FAIL = "R-45095-63572"
"""SQLite: FAIL aborts the statement and keeps its earlier changes."""
ROLLBACK = "R-31881-13880"
"""SQLite: ROLLBACK aborts the statement and rolls back the transaction."""
NO_SUBQUERY = "R-44163-39688"
"""SQLite: a CHECK expression may not contain a subquery."""
ADD_COLUMN = "R-10948-48115"
"""SQLite: ADD COLUMN adds a new column to an existing table."""
FK_OFF = "R-44261-39702"
"""SQLite: foreign key constraints are disabled by default."""
FK_CREATE = "R-08908-23439"
"""SQLite: CREATE TABLE operates the same whether or not foreign keys are enabled."""


def definitions() -> list[QueryCase]:
    """The coverage cases of CHECK constraints and foreign keys."""
    case = QueryCase
    return [
        case("check-fails", TABLES, "INSERT INTO c VALUES(0, 'x');", (FAILS,), ("check", "constraint")),
        case("check-null-passes", TABLES, "INSERT INTO c VALUES(NULL, NULL); SELECT a, t FROM c;", (NULL_PASSES,),
             ("check", "null")),
        case("check-table-constraint", TABLES, "INSERT INTO k VALUES(5, 1);", (EITHER_PLACE,),
             ("check", "table-constraint")),
        case("check-named", TABLES, "INSERT INTO c VALUES(1, 'bad');", (FAILS,), ("check", "named")),
        case("check-numeric-value", TABLES,
             "CREATE TABLE n(a CHECK (a)); INSERT INTO n VALUES('1abc'); INSERT INTO n VALUES(0.5); "
             "INSERT INTO n VALUES('x');", (FAILS,), ("check", "numeric", "create-table-runs")),
        case("check-text-operand", TABLES, "INSERT INTO c VALUES('3x', 'y'); SELECT a FROM c;", (FAILS,),
             ("check", "affinity")),
        case("check-after-not-null", TABLES, "INSERT INTO k VALUES(0, NULL); SELECT a, b FROM k;", (IGNORE, FAILS),
             ("check", "not-null", "order")),
        case("check-before-unique", TABLES, "INSERT INTO u VALUES(1, 9);", (FAILS,), ("check", "unique", "order")),
        case("check-unique-ignored", TABLES, "INSERT INTO u VALUES(1, 2); SELECT k, v FROM u;", (IGNORE,),
             ("check", "unique", "order")),
        case("check-or-ignore", TABLES, "INSERT OR IGNORE INTO c VALUES(0, 'x'), (3, 'y'); SELECT a FROM c;", (IGNORE,),
             ("check", "or-ignore")),
        case("check-or-replace", TABLES, "INSERT OR REPLACE INTO c VALUES(0, 'x');", (REPLACE_ABORTS,),
             ("check", "or-replace")),
        case("check-or-fail", TABLES, "INSERT OR FAIL INTO c VALUES(4, 'y'), (0, 'x'); SELECT a FROM c;", (FAIL,),
             ("check", "or-fail")),
        case("check-or-rollback", TABLES,
             "BEGIN; INSERT INTO p VALUES(2); INSERT OR ROLLBACK INTO c VALUES(0, 'x'); SELECT a FROM p;", (ROLLBACK,),
             ("check", "or-rollback", "transaction")),
        case("check-update", TABLES, "UPDATE c SET a = 0;", (FAILS,), ("check", "update")),
        case("check-update-other-column", TABLES, "UPDATE c SET t = 'cd'; SELECT a, t FROM c;", (FAILS,),
             ("check", "update")),
        case("check-do-update", TABLES, "INSERT INTO u VALUES(1, 3) ON CONFLICT(k) DO UPDATE SET v = 10;", (FAILS,),
             ("check", "on-conflict")),
        case("check-table-conflict-clause", TABLES,
             "CREATE TABLE f(a, CHECK (a > 0) ON CONFLICT IGNORE); INSERT INTO f VALUES(0);", (TABLE_CONFLICT,),
             ("check", "table-constraint", "create-table-runs")),
        case("check-add-column-rows", TABLES, "ALTER TABLE p ADD COLUMN d INTEGER DEFAULT 5 CHECK (d > 9);",
             (ADD_COLUMN,), ("check", "add-column")),
        case("check-add-column-empty", TABLES,
             "CREATE TABLE e(a); ALTER TABLE e ADD COLUMN d DEFAULT 5 CHECK (d > 9); INSERT INTO e VALUES(1, 10); "
             "SELECT a, d FROM e;", (ADD_COLUMN,), ("check", "add-column", "create-table-runs")),
        case("check-add-column-later-rows", TABLES,
             "ALTER TABLE p ADD COLUMN d INTEGER DEFAULT 10 CHECK (d > 9); INSERT INTO p VALUES(2, 3);", (ADD_COLUMN,),
             ("check", "add-column")),
        case("create-table-runs-keys", TABLES,
             "CREATE TABLE n(a INTEGER PRIMARY KEY, b TEXT UNIQUE NOT NULL DEFAULT 'x'); INSERT INTO n(a) VALUES(1); "
             "INSERT INTO n(a) VALUES(2);", (FK_CREATE,), ("create-table-runs", "unique", "default")),
        case("create-table-runs-without-rowid", TABLES,
             "CREATE TABLE w(k TEXT PRIMARY KEY, v) WITHOUT ROWID; INSERT INTO w VALUES('b', 1), ('a', 2); "
             "SELECT k FROM w;", (FK_CREATE,), ("create-table-runs", "without-rowid")),
        case("check-name-carries", TABLES,
             "CREATE TABLE f(a CONSTRAINT x CHECK (a > 0), CHECK (a < 9)); INSERT INTO f VALUES(10);", (FAILS,),
             ("check", "named", "create-table-runs")),
        case("check-double-quoted-column", TABLES,
             "CREATE TABLE f(a CHECK (\"a\" > 0), b CHECK (f.b IS NOT 0)); INSERT INTO f VALUES(0, 1);", (FAILS,),
             ("check", "quoted", "create-table-runs")),
        case("foreign-key-inert", TABLES, "INSERT INTO r VALUES(1, 99); SELECT a, b FROM r;", (FK_OFF,),
             ("foreign-key", "inert")),
        case("foreign-key-list", TABLES,
             "CREATE TABLE f(a REFERENCES k(a) ON DELETE CASCADE ON UPDATE SET NULL ON DELETE RESTRICT, b, c, "
             "FOREIGN KEY (c, b) REFERENCES u(k, v) MATCH FULL DEFERRABLE INITIALLY DEFERRED, "
             "FOREIGN KEY (b) REFERENCES nothere ON UPDATE CASCADE); ALTER TABLE f ADD COLUMN d REFERENCES k;",
             (FK_CREATE,), ("foreign-key", "catalog", "create-table-runs", "add-column")),
        case("foreign-key-one-column", TABLES, "CREATE TABLE f(a REFERENCES k(a, b));", (FK_CREATE,),
             ("foreign-key", "prepare-error")),
        case("foreign-key-column-count", TABLES, "CREATE TABLE f(a, b, FOREIGN KEY (a, b) REFERENCES k(a));",
             (FK_CREATE,), ("foreign-key", "prepare-error")),
        case("foreign-key-unknown-column", TABLES, "CREATE TABLE f(a, FOREIGN KEY (zz) REFERENCES k(a));",
             (FK_CREATE,), ("foreign-key", "prepare-error")),
        case("check-no-such-column", TABLES, "CREATE TABLE f(a CHECK (zz > 0));", (NO_SUBQUERY,),
             ("check", "prepare-error")),
        case("check-aggregate", TABLES, "CREATE TABLE f(a CHECK (count(*) > 0));", (NO_SUBQUERY,),
             ("check", "prepare-error")),
        case("check-after-definition-errors", TABLES, "CREATE TABLE f(a CHECK (zz > 0), a);", (NO_SUBQUERY,),
             ("check", "prepare-error", "order")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `checks`."""
    return query_records(definitions() if cases is None else cases, part="checks")
