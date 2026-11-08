"""Bounded ADR 0027 experiments check existing SELECT rules and expose their limits."""

from pathlib import Path

import pytest

from tests.surface_assertion_examples_test import check_module_chain

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.timeout(180)]


def test_select_collection_rules(runtime_root: Path, tmp_path: Path) -> None:
    """The model's simple SELECT, aggregate and window rules distinguish collection properties,
    WHERE facts, empty groups and alternative results; every retained proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("SelectAutomationCore", 7),), timeout=60)


def test_select_schema_bridge(runtime_root: Path, tmp_path: Path) -> None:
    """The table-output rule proves non-NULL projection over arbitrary valid databases; successful
    empty and populated witnesses rule out an empty-only observation. The current sql_auto attempt
    with the database NOT NULL fact fails before the explicit semantic proof succeeds."""
    check_module_chain(runtime_root, tmp_path, (
        ("SelectAutomationCore", 7), ("SelectAutomationSchema", 3)), timeout=60)


def test_select_nested_sources_and_joins(runtime_root: Path, tmp_path: Path) -> None:
    """Indexed sources require complete-row certainty and clean faults; the real join evaluator
    concatenates inner rows and adds NULL for unmatched outer rows."""
    check_module_chain(runtime_root, tmp_path, (
        ("SelectAutomationCore", 7), ("SelectAutomationSources", 5)), timeout=60)


def test_select_execution_success_and_vacuity(runtime_root: Path, tmp_path: Path) -> None:
    """Sql.check covers every output choice, rejects modeled errors as success and rejects
    unsupported stops; a false-precondition triple exposes the separate vacuity risk."""
    check_module_chain(runtime_root, tmp_path, (("SelectAutomationExecution", 8),), timeout=60)
