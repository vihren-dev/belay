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


def test_replaced_run_contracts(runtime_root: Path, tmp_path: Path) -> None:
    """The original success, empty, failure and unmodeled run laws follow under the original premises."""
    check_module_chain(runtime_root, tmp_path, (
        ("ReplacedSelectRuns", 2), ("ReplacedCalmRuns", 4), ("ReplacedOverflowRuns", 2), ("ReplacedFailedRuns", 3),
    ), timeout=60)


def test_replaced_observation_contracts(runtime_root: Path, tmp_path: Path) -> None:
    """Derive the original resolution-premise contracts from Script.outputOn_resolved, Script.outputIn_resolved,
    Holds/Empty/Fails.iff_query, Holds.inContext_iff_reached and the two Sql.EquivAt IN/EXISTS laws."""
    check_module_chain(runtime_root, tmp_path, (
        ("ReplacedObservations", 4), ("ReplacedRowPredicates", 3), ("ReplacedSubqueryEquivalence", 4),
    ), timeout=60)


def test_replaced_certificate_contracts(runtime_root: Path, tmp_path: Path) -> None:
    """Check the original ReadCertificate preservation, commutation, frame and observation contracts.
    KeptRead.preserves and the single-statement branch rules recover their former resolver premises."""
    check_module_chain(runtime_root, tmp_path, (
        ("ReplacedCertificateObligations", 3), ("ReplacedCertificateClaims", 5), ("ReplacedSiteOutputs", 3), ("ReplacedExecutionProjections", 6), ("ReplacedCertificateChecks", 5),
    ), timeout=60)


def test_replaced_site_certificates(runtime_root: Path, tmp_path: Path) -> None:
    """Site.LookupMove, Site.ReadPreserved, queryTranslates and queryPreserves recover the earlier claims,
    as do preserves_of_check and preserves_of_check_forall for catalog checks."""
    check_module_chain(runtime_root, tmp_path, (
        ("ReplacedSiteCertificates", 2), ("ReplacedSiteClaims", 5), ("ReplacedSiteCheckers", 2),
    ), timeout=60)
