"""Authored coverage cases of DELETE (ADR 0012, amendment 1, slice 3c).

Each rule has a case and a neighbor: DELETE of some rows, of every row and of no row;
a filter that is NULL for some rows; `AND`, `OR`, `IS` and `IS NULL` filters; RETURNING
of the old rows with `*`, expressions and aliases; INSERT after DELETE, whose rowid
comes from the remaining rows, also after the largest rowid is deleted; DELETE in a
transaction that is rolled back; and the prepare errors of the filter and RETURNING.
Native SQLite is the only source of outcomes. The cases use
`conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

ROWS = ("CREATE TABLE d(k INTEGER UNIQUE, v INTEGER, w TEXT, c); "
        "INSERT INTO d VALUES(1, 10, 'a', 1.0), (2, 20, 'b', NULL), (3, NULL, 'c', 3);")
"""Three rows with a unique integer key, an INTEGER column that is NULL in one row, a
TEXT column and an untyped column that is NULL in one row and holds the REAL 1.0."""

DELETE_RULES = ("R-26300-50198", "R-23360-48280")
"""SQLite: a row is deleted when the WHERE expression is true, and kept when it is false or NULL."""


def definitions() -> list[QueryCase]:
    """The coverage cases of DELETE."""
    case = QueryCase
    return [
        case("delete-some-rows", ROWS, "DELETE FROM d WHERE k >= 2;", DELETE_RULES, ("delete", "filter")),
        case("delete-every-row", ROWS, "DELETE FROM d;", ("R-20205-17349",), ("delete", "every-row")),
        case("delete-no-row", ROWS, "DELETE FROM d WHERE k = 99 RETURNING k;", ("R-58129-20729",),
             ("delete", "empty-result")),
        case("delete-null-filter", ROWS, "DELETE FROM d WHERE v > 15 RETURNING k;", DELETE_RULES, ("delete", "null")),
        case("delete-and-or-filter", ROWS,
             "DELETE FROM d WHERE (k = 1 OR k = 3) AND w IS NOT NULL RETURNING k;", DELETE_RULES,
             ("delete", "and-or")),
        case("delete-is-filter", ROWS, "DELETE FROM d WHERE c IS NULL OR c IS 3 RETURNING k;", DELETE_RULES,
             ("delete", "is")),
        case("delete-real-equals-integer", ROWS, "DELETE FROM d WHERE c = 1 RETURNING k;", ("R-29765-45832",),
             ("delete", "real-equals-integer")),
        case("delete-returning-old-rows", ROWS, "DELETE FROM d WHERE k <= 2 RETURNING *, v * 2 AS twice, w;",
             ("R-45416-45177",), ("delete", "returning")),
        case("delete-then-insert", ROWS, "DELETE FROM d WHERE k = 1; INSERT INTO d VALUES(4, 40, 'd', NULL);",
             ("R-29538-34987",), ("delete", "rowid")),
        case("delete-largest-then-insert", ROWS,
             "DELETE FROM d WHERE k = 3; INSERT INTO d VALUES(5, 50, 'e', NULL);",
             ("R-29538-34987",), ("delete", "rowid", "largest")),
        case("delete-rolled-back", ROWS, "BEGIN; DELETE FROM d; ROLLBACK;", ("R-20205-17349",),
             ("delete", "transaction")),
        case("delete-missing-table", ROWS, "DELETE FROM missing;", ("R-25149-16900",), ("delete", "prepare-error")),
        case("delete-missing-column", ROWS, "DELETE FROM d WHERE missing = 1;", ("R-25149-16900",),
             ("delete", "prepare-error")),
        case("delete-aggregate-in-filter", ROWS, "DELETE FROM d WHERE count(*) > 0;", ("R-34076-18298",),
             ("delete", "prepare-error")),
        case("delete-returning-missing-column", ROWS, "DELETE FROM d RETURNING missing;", ("R-25149-16900",),
             ("delete", "returning", "prepare-error")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `deletes`."""
    return query_records(definitions() if cases is None else cases, part="deletes")
