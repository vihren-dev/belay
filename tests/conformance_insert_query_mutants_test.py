"""Mutants of INSERT from a query change the classification of their native cases (ADR 0019, D4)."""

from pathlib import Path

import pytest

from conformance import authored_insert_queries, insert_query_mutants
from conformance.native_replay import prepare
from conformance.resolve_mutants import AGREE, UNSUPPORTED, measure
from conformance.sql_text import runtime_translator

pytestmark = [pytest.mark.integration, pytest.mark.conformance,
              pytest.mark.requires_lean, pytest.mark.requires_native("translation-program", "sqlite3")]
ROOT = Path(__file__).resolve().parents[1]
"""The packages copied by the existing mutant runner."""


@pytest.mark.parametrize("name", list(insert_query_mutants.MUTANTS))
def test_insert_query_mutant_changes_a_verdict(runtime_root: Path, name: str) -> None:
    """Each rule of INSERT from a query (the orders of the source, streaming or collecting, the
    transfer optimization, the output of a source failure) is observable through native verdicts.
    Each invocation changes one rule, so the test runs one mutation build at a time."""
    wanted = insert_query_mutants.TARGETS[name]
    raw = authored_insert_queries.records([case for case in authored_insert_queries.definitions() if case.name in wanted])
    cases = []
    for record in raw:
        case, answer = prepare(record, runtime_translator(runtime_root))
        assert case is not None, answer
        cases.append(case)
    expected = UNSUPPORTED if name in insert_query_mutants.BOUNDARIES else AGREE
    result = measure(cases, ROOT, runtime_root, {name: insert_query_mutants.MUTANTS[name]}, {name: wanted},
                     expected=expected)
    assert result[name]["killed"], result
