"""Each mutant of `conformance.query_mutants`, `conformance.number_mutants`,
`conformance.write_mutants` and `conformance.row_write_mutants` changes the verdict of an
authored case.

ADR 0012 requires that the conformance suite tests each rule of query semantics and
resolution, and slices 2 to 3b add the number and write rules: a changed copy of the
model that no case notices shows a missing case. The cases are the authored cases of
`conformance.authored_queries`, `conformance.authored_numbers`,
`conformance.authored_writes` and `conformance.authored_row_writes`, recorded natively
with their outputs. Two measurements, one for queries and numbers and one for writes,
each build one base copy for their mutants, which keeps each test within its time
limit on a hosted runner; every case must agree with the base copy. Each mutant copy then classifies the case that the mutant names
as its target, which keeps the elaboration of case terms short.
"""

from pathlib import Path
from types import ModuleType

import pytest

from conformance import authored_numbers, authored_queries, authored_row_writes, authored_writes
from conformance.native_replay import prepare
from conformance import number_mutants, query_mutants, row_write_mutants, write_mutants
from conformance.case_format import Json
from conformance.record_parser import runtime_library
from conformance.resolve_mutants import measure

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("parser-library", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]


def measure_set(runtime_root: Path, records: list[dict[str, Json]], tables: list[ModuleType]) -> None:
    """Every case of the records agrees with the unchanged model, and every mutant of the mutant
    tables changes the verdict of its target case."""
    library = runtime_library(runtime_root)
    cases = []
    for record in records:
        case, answer = prepare(record, library)
        assert case is not None, (record["name"], answer)
        cases.append(case)
    mutants: dict[str, tuple[str, str, str]] = {}
    targets: dict[str, tuple[str, ...]] = {}
    for table in tables:
        assert not set(table.MUTANTS) & set(mutants), "mutant names must be unique"
        mutants |= table.MUTANTS
        targets |= table.TARGETS
    result = measure(cases, ROOT, runtime_root, mutants, targets)
    assert set(result) == set(mutants)
    survivors = [name for name, item in result.items() if not item["killed"]]
    assert not survivors, f"mutants that no case notices (add a case for each): {survivors}"


def test_every_query_and_number_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The mutants of query semantics and numbers, against the query and number cases."""
    measure_set(runtime_root, authored_queries.records() + authored_numbers.records(), [query_mutants, number_mutants])


def test_every_write_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """The mutants of writes with output and of row-dependent writes, against the write cases."""
    measure_set(runtime_root, authored_writes.records() + authored_row_writes.records(),
                [write_mutants, row_write_mutants])
