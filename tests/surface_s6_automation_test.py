"""The tactic `sql_run` of ADR 0017, S6, reduces programs to the public rules and leaves honest obligations."""

from pathlib import Path

import pytest

from tests.surface_assertion_examples_test import check_module_chain

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

CHAIN_TIMEOUT_SECONDS = 400
"""The time limit of one fixture module, in seconds. The fixtures use kernel evaluation of small programs."""


def test_sql_run_proves_the_insertion_claim_and_its_triple(runtime_root: Path, tmp_path: Path) -> None:
    """`sql_run` reduces the guide's insertion program (a query, a branch, an insert) to goals about the model's
    coverage and the final property, for the fresh-run claim and for the triple that `mvcgen` unfolds. Each
    claim also has a proof with `Sql.check_single_select` and `Sql.check_send_plainInsert` alone, and all
    three proofs use only ordinary logical axioms."""
    check_module_chain(runtime_root, tmp_path, (("AddCustomerQueries", 0), ("S6AutoAddCustomer", 3)),
                       timeout=CHAIN_TIMEOUT_SECONDS)


def test_sql_run_proves_an_update_claim(runtime_root: Path, tmp_path: Path) -> None:
    """`sql_run` proves the stored row of an UPDATE on a concrete database for every complete environment, and
    the same claim has a proof with `Sql.check_send_plainUpdate` alone."""
    check_module_chain(runtime_root, tmp_path, (("S6RulesEffects", 3), ("S6AutoEffects", 2)),
                       timeout=CHAIN_TIMEOUT_SECONDS)


def test_sql_run_covers_every_statement_rule(runtime_root: Path, tmp_path: Path) -> None:
    """`sql_run` applies `Sql.check_send_plainDelete`, `Sql.check_send_addColumn`, `Sql.check_query_select`,
    `Sql.check_single_select` and `Sql.check_send_select`, and it keeps the sibling goal of a conjunction while
    it works on the first goal. The claims are about one concrete database and every complete environment."""
    check_module_chain(runtime_root, tmp_path, (("S6RulesEffects", 3), ("S6AutoPaths", 6)),
                       timeout=CHAIN_TIMEOUT_SECONDS)


def test_sql_run_refuses_unreadable_programs(runtime_root: Path, tmp_path: Path) -> None:
    """`sql_run` fails with a message, and keeps the goal, for a raw execution step and for a variable program.
    After a rule it leaves an unreadable part as a goal and warns. The fixture checks the exact messages."""
    check_module_chain(runtime_root, tmp_path, (("S6AutoShapes", 0),), timeout=CHAIN_TIMEOUT_SECONDS)


def test_sql_commute_proves_the_claim_and_refuses_the_rest(runtime_root: Path, tmp_path: Path) -> None:
    """`sql_commute` proves the preservation claim with `ReadCertificate.preservesAt_send` and the commutation
    claim with `ReadCertificate.commutesOn_send` from an analysis result and obligations. The hints of the weak
    claim leave three premises of the strong claim open. A read of the change counter and a migration under a
    clock that changes leave the premise that is false open, and the fixtures check the messages."""
    check_module_chain(runtime_root, tmp_path, (
        ("S6RulesQueryPattern", 8), ("S6AutoCommute", 3), ("S6RulesNegativeReads", 8),
        ("S6RulesNegativeClock", 2), ("S6AutoCommuteNegative", 0)), timeout=CHAIN_TIMEOUT_SECONDS)


def test_sql_auto_closes_the_goal_with_one_route_and_offers_its_steps(runtime_root: Path, tmp_path: Path) -> None:
    """`sql_auto` proves a UPDATE claim with the route `sql_run`, a preservation claim with the route
    `sql_commute`, and a plain fact with `grind`. The info message holds the explicit steps of the route, and
    a theorem with the steps alone has the same axioms. A false goal, a route that runs out of its share of the
    work limit and a goal with a sibling goal show the failure messages and that the goals stay."""
    check_module_chain(runtime_root, tmp_path, (
        ("S6RulesEffects", 3), ("S6RulesQueryPattern", 8), ("S6AutoAuto", 5)), timeout=CHAIN_TIMEOUT_SECONDS)
