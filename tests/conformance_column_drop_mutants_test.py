"""Mutants of ALTER TABLE DROP COLUMN change the verdict of their native cases (ADR 0019, D4)."""

from pathlib import Path

import pytest

from conformance import authored_column_drops, column_drop_mutants
from conformance.native_replay import prepare
from conformance.resolve_mutants import AGREE, measure
from conformance.sql_text import runtime_translator

pytestmark = [pytest.mark.integration, pytest.mark.conformance,
              pytest.mark.requires_lean, pytest.mark.requires_native("translation-program", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]
"""The packages copied by the existing mutant runner."""


@pytest.mark.parametrize("name", list(column_drop_mutants.MUTANTS))
def test_column_drop_mutant_changes_a_verdict(runtime_root: Path, name: str) -> None:
    """Each rule of the drops (the checks on the column, the schema tests after the edit, the
    rows, the guard of the run) is observable
    through native verdicts. Each invocation changes one rule, so the test runs one mutation build at a time."""
    wanted = column_drop_mutants.TARGETS[name]
    raw = authored_column_drops.records([case for case in authored_column_drops.definitions() if case.name in wanted])
    cases = []
    for record in raw:
        case, answer = prepare(record, runtime_translator(runtime_root))
        assert case is not None, answer
        cases.append(case)
    result = measure(cases, ROOT, runtime_root, {name: column_drop_mutants.MUTANTS[name]}, {name: wanted}, expected=AGREE)
    assert result[name]["killed"], result
