"""`#sql_check` finds the data loss of a migration that depends on a value in a row: the split of
`customers` by age loses a customer whose age is NULL (fixture `SplitByAge`)."""

import re
import shutil
from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.s6_check_support import CHAIN_TEST_TIMEOUT_SECONDS, false_answer, final_rows, replays
from tests.surface_assertion_examples_test import check_module_chain

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

SPLIT_BY_AGE_MODULES = (("SplitByAge", 1),)
"""The fixture modules in import order, each with its count of `#print axioms` reports."""

LOST_CUSTOMER = re.compile(r"customers:\n  id \| name \| age\n  1  \| ''   \| NULL\n")
"""The table of the counterexample: one customer whose age is NULL."""


def split_by_age_answer(runtime_root: Path, tmp_path: Path) -> str:
    """Compile the fixture modules, audit their axioms, and give the false answer of the check in the
    module `SplitByAge`, from `SQL check: false.` on."""
    output = check_module_chain(runtime_root, tmp_path, SPLIT_BY_AGE_MODULES, timeout=300, output_of="SplitByAge")
    start = output.rfind("\n", 0, output.index("warning: SQL check: false.")) + 1
    return false_answer(output[start:].split("\n'SplitByAge.", 1)[0])


@pytest.mark.timeout(CHAIN_TEST_TIMEOUT_SECONDS)
def test_check_finds_the_customer_whose_age_is_null(runtime_root: Path, tmp_path: Path) -> None:
    """The counterexample search of `#sql_check` (`SqlCheckCommand`) answers `false` for
    `splitByAge preserves allCustomers on shop`, with one customer whose age is NULL: the read gives the
    customer before the migration and no row after it, and every statement of the migration succeeds.
    The fixture also proves with the kernel that the migration loses the customer of the counterexample
    and that the fixed migration keeps it, and refutes the claim with `sql_refute`. Every theorem uses
    only logical axioms."""
    answer = split_by_age_answer(runtime_root, tmp_path)
    assert answer.startswith("SQL check: false.\n"), answer
    assert LOST_CUSTOMER.search(answer), answer
    assert "First program: returns a value; outputs [rows [[1, \"\", null]]].\n" in answer, answer
    assert "Second program: returns a value; outputs [" + "done 0, " * 8 + "rows []].\n" in answer, answer
    assert "INSERT INTO adults SELECT id, name, age FROM customers WHERE age >= 18\n" in answer, answer


@pytest.mark.timeout(CHAIN_TEST_TIMEOUT_SECONDS)
@pytest.mark.requires_native("sqlite3")
def test_native_sqlite_loses_the_customer_too(runtime_root: Path, tmp_path: Path) -> None:
    """The replay script of the false answer (`ReplayScript`) runs in pinned native SQLite 3.51.0: the
    read gives the customer whose age is NULL before the migration, every statement of the migration
    succeeds, and the read after it gives no row."""
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    version = run_command([sqlite, "-version"], cwd=tmp_path, timeout=5)
    assert version.returncode == 0 and version.stdout.startswith("3.51.0 "), version.diagnostic()
    answer = split_by_age_answer(runtime_root, tmp_path)
    before, after = replays(answer)
    assert final_rows(sqlite, tmp_path, "before", before, "") == [[1, "", None]], before
    read = "SELECT id, name, age FROM customers;\n"
    assert final_rows(sqlite, tmp_path, "after", after, read) == [], after
