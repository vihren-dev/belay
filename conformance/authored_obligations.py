"""Boundary cases of the former key obligations (task of 2026-10-14, restriction registry).

Each case starts from a native state that the model's integer keys could not describe: a
REAL value that equals an integer, stored in a unique key column without affinity. Until
slice 5a the admission obligations kept the cases `MODEL_UNSUPPORTED`, and the mutants of
`conformance.obligation_mutants` made them disagree. Since slice 5a (ADR 0012, amendment
4) the model compares keys as SQLite does, and the cases agree with native SQLite, which
compares INTEGER and REAL values numerically. They are frozen as corpus 10. Native
SQLite is the only source of outcomes. The cases use
`conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

NUMERIC_COMPARISON = "R-29765-45832"
"""SQLite: an INTEGER or REAL compared to another INTEGER or REAL is compared numerically."""

KEYED = "CREATE TABLE k(id INTEGER, u UNIQUE); INSERT INTO k VALUES(1, 1.0), (2, 2);"
"""A unique key column without affinity that holds the REAL 1.0 and the integer 2."""


def definitions() -> list[QueryCase]:
    """The boundary cases of the former key obligations of INSERT and UPDATE."""
    case = QueryCase
    return [
        case("insert-key-real-equals-integer", KEYED, "INSERT INTO k VALUES(3, 1);", (NUMERIC_COMPARISON,),
             ("obligation", "insert", "unique")),
        case("update-key-real-equals-integer", KEYED, "UPDATE k SET u = 1 WHERE id = 2;", (NUMERIC_COMPARISON,),
             ("obligation", "update", "unique")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `obligations`."""
    return query_records(definitions() if cases is None else cases, part="obligations")
