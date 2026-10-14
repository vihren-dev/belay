"""Each mutant of `conformance.query_mutants` and `conformance.number_mutants` changes the
verdict of an authored case.

ADR 0012 requires that the conformance suite tests each rule of query semantics and
resolution, and slice 2 adds the number rules: a changed copy of the model that no
case notices shows a missing case. The cases are the authored cases of
`conformance.authored_queries`, `conformance.authored_numbers` and
`conformance.authored_writes`, recorded natively
with their outputs. One measurement builds one base copy for all mutants; every case
must agree with it. Each mutant copy then classifies the case that the mutant names
as its target, which keeps the elaboration of case terms short.
"""

from pathlib import Path

import pytest

from conformance import authored_numbers, authored_queries, authored_writes
from conformance.native_replay import prepare
from conformance.number_mutants import MUTANTS as NUMBER_MUTANTS, TARGETS as NUMBER_TARGETS
from conformance.query_mutants import MUTANTS as QUERY_MUTANTS, TARGETS as QUERY_TARGETS
from conformance.write_mutants import MUTANTS as WRITE_MUTANTS, TARGETS as WRITE_TARGETS
from conformance.record_parser import runtime_library
from conformance.resolve_mutants import measure

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("parser-library", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]


def test_every_query_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """Every case agrees with the unchanged model, and every mutant changes the verdict of its target case."""
    library = runtime_library(runtime_root)
    cases = []
    for record in authored_queries.records() + authored_numbers.records() + authored_writes.records():
        case, answer = prepare(record, library)
        assert case is not None, (record["name"], answer)
        cases.append(case)
    names = [*QUERY_MUTANTS, *NUMBER_MUTANTS, *WRITE_MUTANTS]
    assert len(names) == len(set(names)), "mutant names must be unique"
    mutants = QUERY_MUTANTS | NUMBER_MUTANTS | WRITE_MUTANTS
    result = measure(cases, ROOT, runtime_root, mutants, QUERY_TARGETS | NUMBER_TARGETS | WRITE_TARGETS)
    assert set(result) == set(mutants)
    survivors = [name for name, item in result.items() if not item["killed"]]
    assert not survivors, f"mutants that no case notices (add a case for each): {survivors}"
