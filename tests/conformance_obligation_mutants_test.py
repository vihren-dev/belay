"""Each obligation mutant of `conformance.obligation_mutants` makes its boundary case disagree.

The admission obligations (`LiteralData.insertReady`, `updateReady`) keep native states
out of the model that it would describe wrongly. The boundary cases of
`conformance.authored_obligations`, recorded natively, are `MODEL_UNSUPPORTED` with the
unchanged model; a copy of the model without one conjunct must make its case disagree
with native SQLite, which shows that the conjunct is needed and that the case tests it.
This suite is scheduled (main pushes and nightly runs), not part of pull request CI.
"""

from pathlib import Path

import pytest

from conformance import authored_obligations
from conformance.native_replay import prepare
from conformance.obligation_mutants import MUTANTS, TARGETS
from conformance.record_parser import runtime_library
from conformance.resolve_mutants import UNSUPPORTED, measure

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("parser-library", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]


def test_every_obligation_mutant_makes_its_boundary_case_disagree(runtime_root: Path) -> None:
    """Every boundary case is unsupported with the unchanged model, and every mutant makes its target disagree."""
    library = runtime_library(runtime_root)
    cases = []
    for record in authored_obligations.records():
        case, answer = prepare(record, library)
        assert case is not None, (record["name"], answer)
        cases.append(case)
    result = measure(cases, ROOT, runtime_root, MUTANTS, TARGETS, expected=UNSUPPORTED)
    assert set(result) == set(MUTANTS)
    survivors = [name for name, item in result.items() if not item["killed"]]
    assert not survivors, f"mutants that no boundary case notices (add a case for each): {survivors}"
    other = {name: item["changed"] for name, item in result.items()
             if not all(".disagree" in str(verdict) for verdict in item["changed"].values())}
    assert not other, f"mutants that change a boundary case to a verdict other than DISAGREE: {other}"
