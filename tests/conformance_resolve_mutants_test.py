"""Each mutant of `conformance.resolve_mutants` changes the verdict of an authored model case.

ADR 0008 requires that the conformance suite tests each rule of name resolution:
a changed copy of `resolve` (and of transaction control) that no case notices
shows a missing case. The cases are the authored model cases of
`conformance/model_cases.py`, recorded natively, except the 2,000-column case,
whose rules the lowered-limit cases check.
"""

from pathlib import Path

import pytest

from conformance.model_check import acquire
from conformance.pipeline import fixtures
from conformance.resolve_mutants import MUTANTS, measure

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("translation-program", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]


def test_every_mutant_changes_a_verdict(runtime_root: Path) -> None:
    """Every case agrees with the unchanged model, and every mutant changes at least one verdict."""
    cases = []
    for fixture in fixtures():
        if fixture.name != "limit_before_duplicate":
            case, error = acquire(fixture, runtime_root)
            assert case is not None, error
            cases.append(case)
    result = measure(cases, ROOT, runtime_root)
    assert set(result) == set(MUTANTS)
    survivors = [name for name, item in result.items() if not item["killed"]]
    assert not survivors, f"mutants that no case notices (add a case for each): {survivors}"
