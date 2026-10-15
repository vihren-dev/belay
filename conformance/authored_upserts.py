"""Authored coverage cases of UPSERT (ADR 0012, amendment 4, slice 5c).

The cases follow the "Tests" list of the slice 5c task: DO NOTHING and DO UPDATE, with
and without a target; a target in another order and case, a composite target, a rowid
alias target, and targets that match no key or name no column; `excluded` after
affinity, of an omitted column and of a NULL alias; `WHERE` true, false and NULL; rows
in order; clause order; a row that conflicts on a targeted and an untargeted key; NOT
NULL before conflict handling; DO UPDATE that moves a key or the alias, and that fails
a key, NOT NULL or the alias; and `RETURNING` and the change count of mixed rows. The
UPSERT page of SQLite has no requirement marks, so the cases cite the requirements of
`RETURNING`, of unique keys and of rowid aliases; native SQLite is the only source of
outcomes. The cases use `conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE t(k INTEGER UNIQUE, u INTEGER UNIQUE, v TEXT NOT NULL); "
          "CREATE TABLE c(a INTEGER, b TEXT, n INTEGER, PRIMARY KEY(a, b)); "
          "CREATE TABLE i(id INTEGER PRIMARY KEY, v); CREATE TABLE ia(id INTEGER PRIMARY KEY, k UNIQUE, v); "
          "CREATE TABLE s(k UNIQUE, v); "
          "INSERT INTO t VALUES(1, 1, 'a'), (2, 2, 'b'); INSERT INTO c VALUES(1, 'x', 0); "
          "INSERT INTO i VALUES(1, 'a'); INSERT INTO ia VALUES(1, 1, 'a'); INSERT INTO s VALUES(1, 'a');")
"""A table with two keys and a NOT NULL column, a composite primary key, a rowid alias
alone and with a second key, and a key without affinity."""

RETURNING = "R-15195-28467"
"""SQLite: a RETURNING clause for an UPSERT reports both inserted and updated rows."""
UNIQUE = "R-30981-64168"
"""SQLite: each row must hold a unique combination of values in the columns of a UNIQUE constraint."""
ALIAS = "R-38485-20010"
"""SQLite: a column of type INTEGER PRIMARY KEY becomes an alias for the rowid."""


def definitions() -> list[QueryCase]:
    """The coverage cases of UPSERT."""
    case = QueryCase
    clauses = ("ON CONFLICT(k) DO UPDATE SET v = 'byk' ON CONFLICT(u) DO UPDATE SET v = 'byu' RETURNING *;")
    return [
        case("upsert-nothing-conflict", TABLES, "INSERT INTO t VALUES(1, 9, 'x') ON CONFLICT(k) DO NOTHING RETURNING *;",
             (RETURNING,), ("upsert", "nothing")),
        case("upsert-nothing-insert", TABLES, "INSERT INTO t VALUES(3, 3, 'c') ON CONFLICT(k) DO NOTHING RETURNING *;",
             (RETURNING,), ("upsert", "nothing")),
        case("upsert-nothing-no-target", TABLES, "INSERT INTO t VALUES(9, 2, 'x') ON CONFLICT DO NOTHING;",
             (UNIQUE,), ("upsert", "nothing", "no-target")),
        case("upsert-update-excluded", TABLES,
             "INSERT INTO t VALUES(1, 9, 'x') ON CONFLICT(k) DO UPDATE SET v = excluded.v RETURNING *;",
             (RETURNING,), ("upsert", "update", "excluded")),
        case("upsert-update-reads-row", TABLES,
             "INSERT INTO t VALUES(1, 9, 'x') ON CONFLICT(k) DO UPDATE SET u = u + 10 RETURNING *;",
             (RETURNING,), ("upsert", "update")),
        case("upsert-update-qualified", TABLES,
             "INSERT INTO t VALUES(1, 9, 'x') ON CONFLICT(k) DO UPDATE SET u = t.u + excluded.u RETURNING u;",
             (RETURNING,), ("upsert", "update", "excluded")),
        case("upsert-where-true", TABLES,
             "INSERT INTO t VALUES(1, 9, 'x') ON CONFLICT(k) DO UPDATE SET v = 'w' WHERE excluded.u > 5 RETURNING *;",
             (RETURNING,), ("upsert", "update", "where")),
        case("upsert-where-false", TABLES,
             "INSERT INTO t VALUES(1, 9, 'x') ON CONFLICT(k) DO UPDATE SET v = 'w' WHERE excluded.u < 5 RETURNING *;",
             (RETURNING,), ("upsert", "update", "where")),
        case("upsert-where-null", TABLES,
             "INSERT INTO t VALUES(1, 9, 'x') ON CONFLICT(k) DO UPDATE SET v = 'w' WHERE excluded.v = NULL RETURNING *;",
             (RETURNING,), ("upsert", "update", "where")),
        case("upsert-target-order-case", TABLES,
             "INSERT INTO c VALUES(1, 'x', 7) ON CONFLICT(B, a) DO UPDATE SET n = excluded.n RETURNING *;",
             (RETURNING,), ("upsert", "target", "composite")),
        case("upsert-target-no-key", TABLES, "INSERT INTO t VALUES(1, 1, 'x') ON CONFLICT(v) DO NOTHING;",
             (UNIQUE,), ("upsert", "target", "prepare-error")),
        case("upsert-target-part-of-key", TABLES, "INSERT INTO c VALUES(1, 'x', 1) ON CONFLICT(a) DO NOTHING;",
             (UNIQUE,), ("upsert", "target", "prepare-error")),
        case("upsert-target-no-column", TABLES, "INSERT INTO t VALUES(1, 1, 'x') ON CONFLICT(z) DO NOTHING;",
             (UNIQUE,), ("upsert", "target", "prepare-error")),
        case("upsert-alias-target", TABLES,
             "INSERT INTO i VALUES(1, 'b') ON CONFLICT(id) DO UPDATE SET v = excluded.v RETURNING *;",
             (ALIAS, RETURNING), ("upsert", "alias")),
        case("upsert-alias-null-excluded", TABLES,
             "INSERT INTO ia VALUES(NULL, 1, 'b') ON CONFLICT(k) DO UPDATE SET v = excluded.id RETURNING *;",
             (ALIAS, RETURNING), ("upsert", "alias", "excluded")),
        case("upsert-no-target-update-one-key", TABLES,
             "INSERT INTO i VALUES(1, 'b') ON CONFLICT DO UPDATE SET v = 'w' RETURNING *;",
             (ALIAS, RETURNING), ("upsert", "update", "no-target")),
        case("upsert-excluded-affinity", TABLES,
             "INSERT INTO t VALUES('1', 9, 'x') ON CONFLICT(k) DO UPDATE SET v = excluded.k RETURNING k, v;",
             (RETURNING,), ("upsert", "excluded", "affinity")),
        case("upsert-excluded-omitted", TABLES,
             "INSERT INTO s(k) VALUES(1) ON CONFLICT(k) DO UPDATE SET v = excluded.v RETURNING *;",
             (RETURNING,), ("upsert", "excluded")),
        case("upsert-later-row", TABLES,
             "INSERT INTO t VALUES(5, 5, 'p'), (5, 6, 'q') ON CONFLICT(k) DO UPDATE SET v = excluded.v RETURNING *;",
             (RETURNING,), ("upsert", "rows")),
        case("upsert-targeted-before-untargeted", TABLES,
             "INSERT INTO t VALUES(1, 2, 'n') ON CONFLICT(u) DO UPDATE SET v = 'byu' RETURNING *;",
             (UNIQUE, RETURNING), ("upsert", "order")),
        case("upsert-clause-order", TABLES, "INSERT INTO t VALUES(1, 2, 'n') " + clauses, (RETURNING,),
             ("upsert", "order")),
        case("upsert-clause-second", TABLES, "INSERT INTO t VALUES(9, 2, 'n') " + clauses, (RETURNING,),
             ("upsert", "order")),
        case("upsert-no-target-last", TABLES,
             "INSERT INTO t VALUES(9, 2, 'n') ON CONFLICT(k) DO NOTHING ON CONFLICT DO NOTHING RETURNING *;",
             (UNIQUE, RETURNING), ("upsert", "order", "no-target")),
        case("upsert-untargeted-key", TABLES, "INSERT INTO t VALUES(9, 2, 'n') ON CONFLICT(k) DO NOTHING;",
             (UNIQUE,), ("upsert", "constraint")),
        case("upsert-not-null-first", TABLES, "INSERT INTO t VALUES(1, 9, NULL) ON CONFLICT(k) DO NOTHING;",
             (UNIQUE,), ("upsert", "constraint", "not-null")),
        case("upsert-update-key-conflict", TABLES, "INSERT INTO t VALUES(1, 9, 'x') ON CONFLICT(k) DO UPDATE SET u = 2;",
             (UNIQUE,), ("upsert", "update", "constraint")),
        case("upsert-update-not-null", TABLES,
             "INSERT INTO t VALUES(1, 9, 'x') ON CONFLICT(k) DO UPDATE SET v = NULL;",
             (UNIQUE,), ("upsert", "update", "constraint", "not-null")),
        case("upsert-update-moves-key", TABLES,
             "INSERT INTO t VALUES(1, 9, 'x') ON CONFLICT(k) DO UPDATE SET k = 7, u = excluded.u RETURNING *;",
             (UNIQUE, RETURNING), ("upsert", "update", "key")),
        case("upsert-update-moves-alias", TABLES,
             "INSERT INTO i VALUES(1, 'b') ON CONFLICT(id) DO UPDATE SET id = 9 RETURNING *;",
             (ALIAS, RETURNING), ("upsert", "update", "alias")),
        case("upsert-update-alias-mismatch", TABLES,
             "INSERT INTO i VALUES(1, 'b') ON CONFLICT(id) DO UPDATE SET id = 'x';",
             (ALIAS,), ("upsert", "update", "alias", "mismatch")),
        case("upsert-failure-keeps-table", TABLES,
             "INSERT INTO t VALUES(3, 3, 'c'), (1, 9, 'x') ON CONFLICT(k) DO UPDATE SET u = 3;",
             (UNIQUE,), ("upsert", "constraint", "atomic")),
        case("upsert-mixed-rows", TABLES,
             "INSERT INTO t VALUES(1, 9, 'x'), (3, 3, 'c'), (2, 8, 'y') ON CONFLICT(k) "
             "DO UPDATE SET v = excluded.v WHERE excluded.u > 8 RETURNING *;",
             (RETURNING,), ("upsert", "rows", "changes")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `upserts`."""
    return query_records(definitions() if cases is None else cases, part="upserts")
