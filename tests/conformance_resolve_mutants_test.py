"""Each mutant of `conformance.resolve_mutants` changes the verdict of an authored model case.

ADR 0008 requires that the conformance suite tests each rule of name resolution:
a changed copy of `resolve` (and of transaction control) that no case notices
shows a missing case. The cases are the authored model cases of
`conformance/model_cases.py`, recorded natively, except the 2,000-column case,
whose rules the lowered-limit cases check.

Each edited source file is one measurement. The combined eleven-mutant check
exceeded its 300-second hosted limit in PR 295; these disjoint groups retain
every mutant and case while bounding the number of parallel rebuilds.
"""

from pathlib import Path

import pytest

from conformance.model_check import acquire
from conformance.pipeline import fixtures
from conformance.resolve_mutants import MUTANTS, measure

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("translation-program", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize("source_file", sorted({mutant[0] for mutant in MUTANTS.values()}),
                         ids=lambda path: Path(path).stem)
def test_every_mutant_changes_a_verdict(runtime_root: Path, source_file: str) -> None:
    """All authored cases agree with the base; every resolver mutant of this file changes a verdict."""
    mutants = {name: mutant for name, mutant in MUTANTS.items() if mutant[0] == source_file}
    cases = []
    for fixture in fixtures():
        if fixture.name != "limit_before_duplicate":
            case, error = acquire(fixture, runtime_root)
            assert case is not None, error
            cases.append(case)
    result = measure(cases, ROOT, runtime_root, mutants)
    assert set(result) == set(mutants)
    survivors = [name for name, item in result.items() if not item["killed"]]
    assert not survivors, f"mutants that no case notices (add a case for each): {survivors}"
