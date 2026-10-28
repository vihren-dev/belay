"""The SQL checker on the guide's `NOT IN` and `NOT EXISTS` queries (ADR 0017, S6)."""

import shutil
from pathlib import Path

import pytest

from tests.s6_check_support import CHAIN_TEST_TIMEOUT_SECONDS, CHAIN_TIMEOUT_SECONDS, final_rows, replays, split_blocks
from tests.surface_assertion_examples_test import check_module_chain

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.requires_native("sqlite3"), pytest.mark.timeout(CHAIN_TEST_TIMEOUT_SECONDS)]

NOT_BLOCKED = {"null-blocked": ([], [[1]]), "null-customer": ([], [[None]]), "collations": ([["a"]], [])}
"""The rows that native SQLite gives for `NOT IN` and for `NOT EXISTS`, on each database that refutes their
equivalence."""


def test_not_in_and_not_exists_differ_on_three_databases_and_agree_under_the_premises(
        runtime_root: Path, tmp_path: Path) -> None:
    """The guide's `NOT IN` and `NOT EXISTS` queries are not equivalent: the checker refutes the equivalence on
    a NULL blocked id, on a NULL customer id with a non-NULL blocked id, and on text keys with the collations
    BINARY and NOCASE. Native SQLite gives the rows that the model gives, which differ, and the failing
    observation names the initial database and both outputs. The fixture also shows that the two queries
    agree on one database that meets the sufficient premises (a rowid alias and no NULL blocked id). The
    module `S6NotBlockedLaw` proves the equivalence for every database with the stated site, with the audit of
    its axioms (only `propext`, `Classical.choice` and `Quot.sound`), and shows that the site is satisfiable."""
    output = check_module_chain(runtime_root, tmp_path, (
        ("S6CheckLabels", 0), ("S6NotBlocked", 1), ("S6NotBlockedLaw", 4)),
        timeout=CHAIN_TIMEOUT_SECONDS, output_of="S6NotBlocked")
    found = split_blocks(output)
    assert set(found) == set(NOT_BLOCKED), output
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    for name, (in_rows, exists_rows) in NOT_BLOCKED.items():
        block = found[name]
        assert block.startswith("SQL check: false."), (name, block)
        assert "Failing observation: The actual runs of the two programs differ at this context." in block, block
        first, second = replays(block)
        assert final_rows(sqlite, tmp_path, f"{name}-in", first, "") == in_rows, block
        assert final_rows(sqlite, tmp_path, f"{name}-exists", second, "") == exists_rows, block


PREMISES_HOLD = """CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT, email TEXT);
CREATE TABLE blocked(customer_id INTEGER);
INSERT INTO customers VALUES(1, 'ann', 'a@x'), (2, 'bob', 'b@x');
INSERT INTO blocked VALUES(2);
"""
"""The database `premisesHold` of the fixture `S6NotBlocked`."""


@pytest.mark.parametrize("query", [
    "SELECT id FROM customers WHERE id NOT IN (SELECT customer_id FROM blocked);",
    "SELECT id FROM customers c WHERE NOT EXISTS (SELECT 1 FROM blocked b WHERE b.customer_id = c.id);"])
def test_native_sqlite_gives_the_rows_of_the_fixture_on_the_database_that_meets_the_premises(
        tmp_path: Path, query: str) -> None:
    """Native SQLite gives customer 1 for each of the two guide queries on the database `premisesHold`, the rows
    that the theorem `premisesHold_rows` states for the model. This checks the concrete result of the fixture."""
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    assert final_rows(sqlite, tmp_path, "premises", PREMISES_HOLD + query, "") == [[1]]
