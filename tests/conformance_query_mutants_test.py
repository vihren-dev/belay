"""Each mutant of `conformance.query_mutants` and `conformance.number_mutants` changes the
verdict of an authored case.

ADR 0012 requires that the conformance suite tests each rule of query semantics and
resolution, and slice 2 adds the number rules: a changed copy of the model that no
case notices shows a missing case. The cases are the authored cases of
`conformance.authored_queries` and `conformance.authored_numbers`, recorded natively
with their outputs. One measurement builds one base copy for all mutants.
"""

from pathlib import Path

import pytest

from conformance import authored_numbers, authored_queries
from conformance.native_replay import prepare
from conformance.number_mutants import MUTANTS as NUMBER_MUTANTS
from conformance.query_mutants import MUTANTS as QUERY_MUTANTS
from conformance.record_parser import runtime_library
from conformance.resolve_mutants import measure

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("parser-library", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]


def test_every_query_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """Every case agrees with the unchanged model, and every mutant changes at least one verdict."""
    library = runtime_library(runtime_root)
    cases = []
    for record in authored_queries.records() + authored_numbers.records():
        case, answer = prepare(record, library)
        assert case is not None, (record["name"], answer)
        cases.append(case)
    assert not set(QUERY_MUTANTS) & set(NUMBER_MUTANTS), "mutant names must be unique"
    mutants = QUERY_MUTANTS | NUMBER_MUTANTS
    result = measure(cases, ROOT, runtime_root, mutants)
    assert set(result) == set(mutants)
    survivors = [name for name, item in result.items() if not item["killed"]]
    assert not survivors, f"mutants that no case notices (add a case for each): {survivors}"
