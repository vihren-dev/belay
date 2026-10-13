"""Each mutant of `conformance.query_mutants` changes the verdict of an authored query case.

ADR 0012 requires that the conformance suite tests each rule of query semantics and
resolution: a changed copy of the model that no case notices shows a missing case.
The cases are the authored query cases of `conformance.authored_queries`, recorded
natively with their outputs.
"""

from pathlib import Path

import pytest

from conformance.authored_queries import records
from conformance.native_replay import prepare
from conformance.query_mutants import MUTANTS
from conformance.record_parser import runtime_library
from conformance.resolve_mutants import measure

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("parser-library", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]


def test_every_query_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """Every case agrees with the unchanged model, and every mutant changes at least one verdict."""
    library = runtime_library(runtime_root)
    cases = []
    for record in records():
        case, answer = prepare(record, library)
        assert case is not None, (record["name"], answer)
        cases.append(case)
    result = measure(cases, ROOT, runtime_root, MUTANTS)
    assert set(result) == set(MUTANTS)
    survivors = [name for name, item in result.items() if not item["killed"]]
    assert not survivors, f"mutants that no case notices (add a case for each): {survivors}"
