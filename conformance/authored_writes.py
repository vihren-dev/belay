"""Authored coverage cases of writes with output (ADR 0012, slice 3a).

Each rule of the slice has a case and a neighbor: RETURNING `*`, columns, expressions
and aliases on INSERT (one and several rows, omitted columns) and UPDATE (some rows,
no row, every row); the names of RETURNING columns; a write that fails a NOT NULL or
unique constraint; the prepare errors in RETURNING and the error in VALUES that comes
first; and constant expressions in VALUES, SET and the value of a filter. Native
SQLite is the only source of outcomes. The cases use
`conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLE = ("CREATE TABLE w(a INTEGER UNIQUE, b TEXT, c, d TEXT NOT NULL); "
         "INSERT INTO w VALUES(1, 'one', NULL, 'p'), (2, 'two', 2, 'q');")
"""A table with a unique integer key, a TEXT column, a column without affinity and a NOT
NULL column, with two rows."""


def definitions() -> list[QueryCase]:
    """The coverage cases of writes with output."""
    case = QueryCase
    return [
        case("insert-returning-star", TABLE, "INSERT INTO w VALUES(3, 'three', X'00', 'r') RETURNING *;",
             ("R-46605-62546", "R-45416-45177"), ("returning", "insert", "star")),
        case("insert-without-returning", TABLE, "INSERT INTO w VALUES(3, 'three', X'00', 'r');",
             ("R-45416-45177",), ("insert", "neighbor")),
        case("insert-rows-expressions-aliases", TABLE,
             "INSERT INTO w(a, d) VALUES(4, 's'), (5, 't') RETURNING a, a * 10 AS tens, b, d, A;",
             ("R-20205-54808", "R-02910-05480", "R-45416-45177"), ("returning", "insert", "several-rows", "omitted-column")),
        case("returning-defined-names", TABLE, "INSERT INTO w(a, d) VALUES(6, 'v') RETURNING B, D, c;",
             ("R-25727-24709",), ("returning", "names")),
        case("insert-constant-expressions", TABLE,
             "INSERT INTO w VALUES(1 + 2 * 3, CAST(12 AS TEXT), coalesce(NULL, 7), 'u') RETURNING a, b, c;",
             ("R-41357-61664",), ("insert", "constant-expression")),
        case("update-returning-new-values", TABLE, "UPDATE w SET b = 'changed', c = 10 / 3 WHERE a = 1 RETURNING a, b, c;",
             ("R-13116-43655", "R-63299-18573"), ("returning", "update")),
        case("update-returning-no-row", TABLE, "UPDATE w SET b = 'z' WHERE a = 99 RETURNING b;",
             ("R-45416-45177",), ("returning", "update", "empty-result")),
        case("update-returning-every-row", TABLE, "UPDATE w SET c = NULL RETURNING a, c;", ("R-45416-45177",),
             ("returning", "update", "every-row")),
        case("update-constant-set-and-filter", TABLE,
             "UPDATE w SET b = CAST(5 AS TEXT) WHERE a = 1 + 1 RETURNING a, b;", ("R-41357-61664",),
             ("update", "constant-expression")),
        case("returning-not-null-failure", TABLE, "INSERT INTO w(a, b) VALUES(7, 'x') RETURNING a, b;",
             ("R-45416-45177",), ("returning", "constraint-failure")),
        case("returning-unique-failure", TABLE, "UPDATE w SET a = 2 WHERE a = 1 RETURNING a;", ("R-45416-45177",),
             ("returning", "constraint-failure", "unique")),
        case("returning-aggregate-error", TABLE, "INSERT INTO w VALUES(3, 'x', NULL, 'y') RETURNING count(*);",
             ("R-34076-18298",), ("returning", "prepare-error")),
        case("returning-missing-column", TABLE, "INSERT INTO w VALUES(3, 'x', NULL, 'y') RETURNING missing;",
             ("R-25149-16900",), ("returning", "prepare-error")),
        case("values-error-before-returning", TABLE, "INSERT INTO w VALUES(missing, 'x', NULL, 'y') RETURNING other;",
             ("R-25149-16900",), ("returning", "prepare-error", "two-errors")),
        case("values-aggregate-error", TABLE, "INSERT INTO w VALUES(max(1), 'x', NULL, 'y');", ("R-34076-18298",),
             ("insert", "prepare-error")),
        case("values-coalesce-argument-count", TABLE, "INSERT INTO w VALUES(coalesce(1), 'x', NULL, 'y');",
             ("R-41357-61664",), ("insert", "prepare-error")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `writes`."""
    return query_records(definitions() if cases is None else cases, part="writes")
