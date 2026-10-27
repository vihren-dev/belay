"""Mutants of the table rebuild change the verdict of their native cases (ADR 0019, D4)."""

from pathlib import Path

import pytest

from conformance import authored_rebuilds, rebuild_mutants
from conformance.native_replay import prepare
from conformance.resolve_mutants import AGREE, measure
from conformance.sql_text import runtime_translator

pytestmark = [pytest.mark.integration, pytest.mark.conformance,
              pytest.mark.requires_lean, pytest.mark.requires_native("translation-program", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]
"""The packages copied by the existing mutant runner."""


@pytest.mark.parametrize("name", list(rebuild_mutants.MUTANTS))
def test_rebuild_mutant_changes_a_verdict(runtime_root: Path, name: str) -> None:
    """The rule of the rename in the rebuild (a rename may make the keys of the children
    find a parent) is observable
    through native verdicts. Each invocation changes one rule, so the test runs one mutation build at a time."""
    wanted = rebuild_mutants.TARGETS[name]
    raw = authored_rebuilds.records([case for case in authored_rebuilds.definitions() if case.name in wanted])
    cases = []
    for record in raw:
        case, answer = prepare(record, runtime_translator(runtime_root))
        assert case is not None, answer
        cases.append(case)
    result = measure(cases, ROOT, runtime_root, {name: rebuild_mutants.MUTANTS[name]}, {name: wanted}, expected=AGREE)
    assert result[name]["killed"], result
