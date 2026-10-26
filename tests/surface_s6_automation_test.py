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


def test_sql_run_refuses_unreadable_programs(runtime_root: Path, tmp_path: Path) -> None:
    """`sql_run` fails with a message, and keeps the goal, for a raw execution step and for a variable program.
    After a rule it leaves an unreadable part as a goal and warns. The fixture checks the exact messages."""
    check_module_chain(runtime_root, tmp_path, (("S6AutoShapes", 0),), timeout=CHAIN_TIMEOUT_SECONDS)
