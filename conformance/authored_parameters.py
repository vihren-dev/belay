"""Authored coverage cases of parameters (ADR 0019, slice 1; plans/20261023-parameters.task.md).

The cases follow the "Tests" list of the task: the numbering of outcome 2 with distinct values;
a parameter in each place of outcome 3, also in a write that runs a trigger and in an upsert;
the affinity and collation examples; `ORDER BY ?` and `GROUP BY ?`, also over no rows; `LIMIT ?`
and `OFFSET ?` with each kind of value of outcome 5, the errors included; the prepare errors of
outcome 6; and a script of several statements, each with its own values. Each case gives one
tuple of typed values for each statement that SQLite reaches. Native SQLite is the only source
of outcomes. The cases are in `conformance.authored_parameter_values` and
`conformance.authored_parameter_windows`.
"""

from dataclasses import dataclass
import struct

from conformance.authored_resolution import profile
from conformance.case_format import Json
from conformance.native_connection import Cell
from conformance.native_record import record_sql

NULL: Cell = (5, None)
"""The NULL value of a binding."""


def integer(value: int) -> Cell:
    """The binding of an INTEGER value."""
    return 1, value


def real(value: float) -> Cell:
    """The binding of a REAL value, as the bits of its IEEE 754 double."""
    return 2, struct.unpack("<Q", struct.pack("<d", value))[0]


def text(value: str) -> Cell:
    """The binding of a TEXT value, as its UTF-8 bytes."""
    return 3, value.encode()


def blob(value: bytes) -> Cell:
    """The binding of a BLOB value."""
    return 4, value


@dataclass(frozen=True)
class ParameterCase:
    """One coverage case of parameters: setup and SQL, the requirement identifiers it covers,
    descriptive features, and one tuple of values for each statement that SQLite reaches."""

    name: str
    setup: str
    sql: str
    requirements: tuple[str, ...]
    features: tuple[str, ...]
    parameters: tuple[tuple[Cell, ...], ...]


def definitions() -> list[ParameterCase]:
    """The coverage cases of parameters, in the order of the outcomes of the task."""
    from conformance.authored_parameter_values import value_definitions
    from conformance.authored_parameter_windows import window_definitions
    return value_definitions() + window_definitions()


def records(cases: list[ParameterCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs and its bound values, under
    SQLite's default measured profile, in the part `parameters`."""
    selected = definitions() if cases is None else cases
    measured = profile(())
    return [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements), outputs=True,
                          parameters=list(case.parameters), profile=measured),
             "part": "parameters", "features": list(case.features)}
            for case in selected]
