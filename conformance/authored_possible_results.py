"""Authored coverage cases of the results that SQLite may give (ADR 0018, slice 6).

The cases follow the "Tests" list of the slice 6 task: `LIMIT` and `OFFSET` that cut ties of
`ORDER BY`, also with `DESC` and a collation; `LIMIT` without `ORDER BY` over the guide's table with an
index that changes SQLite's order, as SQLite reads the names from the index; `DISTINCT`, `GROUP BY` and an aggregate query with `LIMIT`; a
window that cuts no tie; and `LIMIT 0`. The runner's comparison checks that the rows that SQLite
gives are among the model's results. Native SQLite is the only source of outcomes. The cases use
`conformance.authored_queries.QueryCase`.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

LIMIT = "R-37911-51642"
"""SQLite: LIMIT places an upper bound on the number of rows returned."""
FIRST_ROWS = "R-33750-29536"
"""SQLite: the SELECT returns the first N rows of its result set."""
OFFSET = "R-20467-43422"
"""SQLite: OFFSET omits the first M rows and returns the next N."""
FEWER_ROWS = "R-34648-44875"
"""SQLite: with fewer than M+N rows, the rows after the first M are returned."""
TIES = "R-44988-41064"
"""SQLite: ties of the first ORDER BY expression are broken by the next one."""
DIRECTION = "R-06617-54588"
"""SQLite: ASC returns smaller values first, DESC larger ones."""
COLLATION = "R-27301-09658"
"""SQLite: an ORDER BY column sorts with the column's collation."""

JOBS = ("CREATE TABLE t(id INTEGER PRIMARY KEY, p INTEGER, name TEXT COLLATE NOCASE); "
        "INSERT INTO t VALUES (1, 1, 'c'), (2, 1, 'a'), (3, 1, 'b'), (4, 2, 'd'), (5, 2, 'e'), (6, 3, 'A');")
"""Jobs whose priorities tie in groups of three, two and one, and names that tie under NOCASE."""


def definitions() -> list[QueryCase]:
    """The coverage cases of the results that SQLite may give."""
    case = QueryCase
    return [
        case("ties-limit", JOBS, "SELECT p, name FROM t ORDER BY p LIMIT 2; SELECT p, name FROM t ORDER BY p LIMIT 4;",
             (LIMIT, FIRST_ROWS, TIES), ("limit", "ties")),
        case("ties-offset", JOBS, "SELECT p, name FROM t ORDER BY p LIMIT 1 OFFSET 1; SELECT p, name FROM t ORDER BY p LIMIT 2 OFFSET 2;",
             (OFFSET, TIES), ("offset", "ties", "two-groups")),
        case("ties-desc", JOBS, "SELECT p, name FROM t ORDER BY p DESC LIMIT 2; SELECT p, id, name FROM t ORDER BY p DESC, id LIMIT 3;",
             (DIRECTION, TIES), ("desc", "ties")),
        case("ties-collation", JOBS, "SELECT name, id FROM t ORDER BY name LIMIT 1; SELECT name, id FROM t ORDER BY name DESC LIMIT 2;",
             (COLLATION, TIES), ("collation", "ties")),
        case("index-order", "CREATE TABLE c(id INTEGER PRIMARY KEY, name TEXT NOT NULL, address TEXT, notes TEXT); "
             "INSERT INTO c VALUES (1, 'bob', 'x', 'y'), (2, 'ada', 'x', 'y'); CREATE INDEX c_name ON c(name);",
             "SELECT name FROM c; SELECT name FROM c LIMIT 1; SELECT 1 FROM c LIMIT 1;",
             (LIMIT, FIRST_ROWS), ("no-order-by", "index")),
        case("distinct-group", JOBS, "SELECT DISTINCT p FROM t LIMIT 2; SELECT p, count(*) FROM t GROUP BY p LIMIT 1 OFFSET 1; "
             "SELECT count(*) FROM t LIMIT 1;",
             (LIMIT, OFFSET), ("distinct", "group-by", "aggregate")),
        case("no-cut", JOBS, "SELECT p, name FROM t ORDER BY p LIMIT 3; SELECT id, name FROM t ORDER BY id LIMIT 2 OFFSET 1; "
             "SELECT p, name FROM t ORDER BY p LIMIT 10 OFFSET 5;",
             (FIRST_ROWS, FEWER_ROWS), ("no-cut",)),
        case("limit-zero", JOBS, "SELECT p, name FROM t ORDER BY p LIMIT 0; SELECT name FROM t LIMIT 0 OFFSET 2;",
             (LIMIT,), ("limit-zero",)),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `possible-results`."""
    return query_records(definitions() if cases is None else cases, part="possible-results")
