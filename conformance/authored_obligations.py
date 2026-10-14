"""Boundary cases of the admission obligations (task of 2026-10-14, restriction registry).

Each case starts from a native state just outside the model's data domain: a REAL value
that equals an integer, stored in a unique key column without affinity, where the model
compares key values only as integers (`LiteralData.keyEqual`). Resolution accepts the statement, so only the obligation conjunct that
`conformance.obligation_mutants` names for the case keeps it `MODEL_UNSUPPORTED`; the
mutant that removes the conjunct makes the case disagree with native SQLite, which
compares INTEGER and REAL values numerically. Native SQLite is the only source of
outcomes. The cases use `conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

NUMERIC_COMPARISON = "R-29765-45832"
"""SQLite: an INTEGER or REAL compared to another INTEGER or REAL is compared numerically."""

KEYED = "CREATE TABLE k(id INTEGER, u UNIQUE); INSERT INTO k VALUES(1, 1.0), (2, 2);"
"""A unique key column without affinity that holds the REAL 1.0 and the integer 2."""


def definitions() -> list[QueryCase]:
    """The boundary cases, one for each obligation conjunct with a mutant."""
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
