"""ADR 0027 SELECT procedure: the goals that `sql_select` leaves, its limits and its trust boundaries."""

from pathlib import Path

import pytest

from tests.surface_assertion_examples_test import check_module_chain

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.timeout(180)]

CORE_CASES = (("SelectProjectionCases", 6), ("SelectFilterCases", 3), ("SelectComparisonCases", 5),
              ("SelectCardinalityCases", 5), ("SelectGroupSupport", 0), ("SelectGroupCases", 6),
              ("SelectCountCases", 5), ("SelectHavingCases", 6), ("SelectOrderCases", 4),
              ("SelectProcedureCases", 9))


def test_residual_goals(runtime_root: Path, tmp_path: Path) -> None:
    """The explanations of `sql_select` (`Belay/Sqlite/SqlSelect.lean`) when it stops (B04, B09), checked as
    text: a goal of an unknown shape is refused; a premise of the execution rule that is not proved stops it
    in the execution phase; arithmetic of the user stops it in the result phase, with the claim as the goal;
    cyclic forward rules end; and a rule without end and cyclic hints stop it at its limit of rule
    applications. A hint whose premise is not proved does not apply. The six residual theorems are then
    proved by hand, and every proof has only logical axioms; the case of the execution rule checks only
    the explanation."""
    check_module_chain(runtime_root, tmp_path, (*CORE_CASES, ("SelectResidualCases", 6)), timeout=90)


def test_trust_boundaries(runtime_root: Path, tmp_path: Path) -> None:
    """The trust boundaries of `sql_select` (`Belay/Sqlite/SqlSelect.lean`, B03, B07): a false precondition
    proves a triple that says nothing about a run; a false claim that a valid database refutes stays open;
    the attribute `sql_select_rule` refuses an axiom; and a proof that uses a rule proved with `sorry`
    depends on `sorryAx`, which the axiom audit of the other proofs rejects."""
    check_module_chain(runtime_root, tmp_path, (*CORE_CASES, ("SelectTrustCases", 3)), timeout=90)


def test_work_limit_and_cancellation(runtime_root: Path, tmp_path: Path) -> None:
    """The work limit and the cancellation of `sql_auto` (`Belay/Sqlite/AutoSearch.lean`) on SELECT claims
    (B06): a call that runs out of a work limit of 300 thousand heartbeats, or that runs with a cancellation
    token that is set, fails, and the claim and its sibling goal stay unchanged and unassigned. The
    interruption reaches the caller. The procedure of `sql_select` inside the route `sql_run` runs out with
    the share of that route, which closes the same check without a limit. Every proof has only logical
    axioms."""
    check_module_chain(runtime_root, tmp_path, (*CORE_CASES, ("SelectBudgetCases", 4)), timeout=90)
