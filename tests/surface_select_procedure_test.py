"""ADR 0027 SELECT procedure: the goals that `sql_select` leaves, its limits and its trust boundaries."""

import json
import re
import shutil
from pathlib import Path

import pytest

from tests.s6_check_support import CHAIN_TEST_TIMEOUT_SECONDS, CHAIN_TIMEOUT_SECONDS, final_rows, replays, split_blocks
from tests.surface_assertion_examples_test import check_module_chain
from tests.surface_replay_test import native_replay

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.timeout(180)]

CORE_CASES = (("SelectProjectionCases", 6), ("SelectFilterCases", 3), ("SelectComparisonCases", 5),
              ("SelectCardinalityCases", 5), ("SelectGroupSupport", 0), ("SelectGroupCases", 6),
              ("SelectCountCases", 5), ("SelectHavingCases", 6), ("SelectOrderCases", 4),
              ("SelectProcedureCases", 9))


def test_residual_goals(runtime_root: Path, tmp_path: Path) -> None:
    """The explanations of `sql_select` (`Belay/Sqlite/{Queries/Automation,Schema/Dispatch,Programs/Automation}/SqlSelect.lean`) when it stops (B04, B09), checked as
    text: a goal of an unknown shape is refused; a premise of the execution rule that is not proved stops it
    in the execution phase; arithmetic of the user stops it in the result phase, with the claim as the goal;
    cyclic forward rules end; and a rule without end and cyclic hints stop it at its limit of rule
    applications. A hint whose premise is not proved does not apply. The six residual theorems are then
    proved by hand, and every proof has only logical axioms; the case of the execution rule checks only
    the explanation."""
    check_module_chain(runtime_root, tmp_path, (*CORE_CASES, ("SelectResidualCases", 6)), timeout=90)


def test_trust_boundaries(runtime_root: Path, tmp_path: Path) -> None:
    """The trust boundaries of `sql_select` (`Belay/Sqlite/{Queries/Automation,Schema/Dispatch,Programs/Automation}/SqlSelect.lean`, B03, B07): a false precondition
    proves a triple that says nothing about a run; a false claim that a valid database refutes stays open;
    the attribute `sql_select_rule` refuses an axiom; and a proof that uses a rule proved with `sorry`
    depends on `sorryAx`, which the axiom audit of the other proofs rejects."""
    check_module_chain(runtime_root, tmp_path, (*CORE_CASES, ("SelectTrustCases", 3)), timeout=90)


def test_work_limit_and_cancellation(runtime_root: Path, tmp_path: Path) -> None:
    """The work limit and the cancellation of `sql_auto` (`Belay/Sqlite/{Programs/Automation,Tooling/Tests}/AutoSearch.lean`) on SELECT claims
    (B06): a call that runs out of a work limit of 300 thousand heartbeats, or that is cancelled by a hint
    that the route `sql_select`, or the procedure inside the route `sql_run`, reads, fails, and the claim
    and its sibling goal stay unchanged and unassigned. The interruption reaches the caller. The procedure
    of `sql_select` inside the route `sql_run` runs out with the share of that route, which closes the same
    check without a limit. Every proof has only logical axioms."""
    check_module_chain(runtime_root, tmp_path, (*CORE_CASES, ("SelectBudgetCases", 5)), timeout=90)


REPLAYED_FALSE = ("convenience-screened", "run-schema-false", "run-witness-false", "run-named-false")
"""The false claims whose counterexample has rows of the query, which native SQLite must give too."""


@pytest.mark.requires_native("sqlite3")
@pytest.mark.timeout(CHAIN_TEST_TIMEOUT_SECONDS)
def test_background_checking(runtime_root: Path, tmp_path: Path) -> None:
    """Background checking of SELECT claims (B10): `#sql_check` proves the A01 claim through the route
    `sql_select` of its search (`Belay/Sqlite/{Programs/Automation,Tooling/Counterexamples}/CheckAutoProof.lean`). It refutes false claims about a run with
    a database from the schema, an explicit database, the database that the claim names and the empty
    database, and a convenience claim with its screen, each with a replay that native SQLite runs to the same
    rows, or to the same missing table. It answers unknown for a true claim with arithmetic that the procedure
    cannot prove, and, with the reason, for a refutation whose run has no script to replay
    (`Belay/Sqlite/{Programs/Claims,Tooling/Counterexamples}/CheckClaim.lean`). An excluded execution rule removes the proof, and a cancellation in the
    search reaches the caller with no result."""
    output = check_module_chain(runtime_root, tmp_path, (*CORE_CASES, ("S6CheckLabels", 0), ("SelectCheckCases", 0)),
                                timeout=CHAIN_TIMEOUT_SECONDS)
    blocks = split_blocks(output)
    assert set(blocks) == {"select-proved", *REPLAYED_FALSE, "run-empty-false", "arithmetic-unknown",
                           "replay-unknown"}, output
    proved = blocks["select-proved"]
    assert proved.startswith("SQL check: proved.") and "sql_select [rfl, ⟨_, _, _, rfl⟩]" in proved, proved
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    for name in REPLAYED_FALSE:
        block = blocks[name]
        assert block.startswith("SQL check: false."), (name, block)
        found = re.search(r"^customerOfFirst: rows (\[.*\])$", block, re.MULTILINE)
        assert found is not None, block
        model_rows = json.loads(found.group(1))
        assert model_rows and final_rows(sqlite, tmp_path, name, replays(block)[0], "") == model_rows, block
    assert "Database: shop\n" in blocks["run-named-false"], blocks["run-named-false"]
    empty = blocks["run-empty-false"]
    assert empty.startswith("SQL check: false.\nDatabase: empty\n") and "customerOfFirst: error 1" in empty, empty
    result = native_replay(sqlite, replays(empty)[0], tmp_path, "run-empty-false")
    assert "no such table: invoices" in result.stderr, result.diagnostic()
    for name in ("arithmetic-unknown", "replay-unknown"):
        assert blocks[name].startswith("SQL check: unknown;") and "Database:" not in blocks[name], blocks[name]
    assert ("the kernel refutes the claim on a database, but the checker could not build its SQLite replay"
            in blocks["replay-unknown"]), blocks["replay-unknown"]
    assert "sql_refute (db := database)" in blocks["replay-unknown"], blocks["replay-unknown"]
    assert "excluded rule: unknown" in output and "cancelled search: interrupted" in output, output
