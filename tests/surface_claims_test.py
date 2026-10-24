"""Claims over every database (ADR 0017, S4; `Belay/Sqlite/QueryBridge.lean`,
`Belay/Sqlite/SelectOneFrom.lean`, `Belay/Sqlite/SqlSimpLaws.lean` and the model's laws of the
expressions of a condition). Each fixture proves its claims for an arbitrary database and checks
each claim on a concrete database, so that no lemma is vacuous. The fixture fails to elaborate
when a proof or an instance does not hold.
"""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_expression_laws_turn_a_condition_into_logic(runtime_root: Path, tmp_path: Path) -> None:
    """The simp set `sql_simp` resolves a written condition (`BETWEEN`, `AND`, `NOT`, `OR`, `IS NULL`,
    a parameter) to the resolved expression with the affinity and collation of its columns, shows
    that the expression is calm, and turns the truth of `AND`, `OR` and `IS NULL` into Booleans."""
    result = run_command(surface_command(runtime_root, FIXTURES / "ClaimsExpressionLaws.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_some_row_of_a_table_satisfies_a_condition(runtime_root: Path, tmp_path: Path) -> None:
    """`SELECT 1 FROM t WHERE p` over every database: a claim proved with the lemmas and `sql_simp`,
    with an instance on one database where `decide +kernel` checks both sides."""
    result = run_command(surface_command(runtime_root, FIXTURES / "ClaimsSelectOne.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_no_row_or_some_row_satisfies_a_condition_in_a_subquery(runtime_root: Path, tmp_path: Path) -> None:
    """`SELECT 1 WHERE [NOT] EXISTS (SELECT 1 FROM t WHERE p)` over every database: a claim proved with the
    lemmas and `sql_simp`, with an instance on one database where `decide +kernel` checks both sides."""
    result = run_command(surface_command(runtime_root, FIXTURES / "ClaimsExists.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_a_where_that_may_fail_has_no_modeled_output(runtime_root: Path, tmp_path: Path) -> None:
    """`SELECT 1 FROM t WHERE abs(x) = 1` (and the same call in a subquery of `EXISTS`) on a table with the
    smallest 64-bit integer and the integer 1: SQLite can fail at the call of `abs` on the smallest integer, so
    the model does not describe the statement. None of `Holds`, `Empty` and `Fails` holds, by `decide +kernel`
    and by the lemmas over every database."""
    result = run_command(surface_command(runtime_root, FIXTURES / "ClaimsMayFail.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_a_query_without_from_holds_or_is_empty_by_its_condition(runtime_root: Path, tmp_path: Path) -> None:
    """`SELECT e [WHERE c]` over every database: `Holds` for a query without `WHERE` and `Empty` for a false
    condition, proved with the lemmas and `sql_simp`, with instances where `decide +kernel` checks the claim."""
    result = run_command(surface_command(runtime_root, FIXTURES / "ClaimsNoFrom.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_the_number_of_rows_of_a_table_is_compared_with_a_parameter(runtime_root: Path, tmp_path: Path) -> None:
    """`SELECT 1 WHERE (SELECT count(*) FROM t [WHERE p]) = $n` over every database: `Holds` means that the
    table has `n` rows (or `n` rows for which `p` is true), proved with the lemmas and `sql_simp`, with instances
    on one database where `decide +kernel` checks the claim for a true and for a false `n`."""
    result = run_command(surface_command(runtime_root, FIXTURES / "ClaimsCount.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_a_parameter_is_in_a_column_of_a_table(runtime_root: Path, tmp_path: Path) -> None:
    """`SELECT 1 WHERE $x IN (SELECT e FROM t [WHERE p])` over every database: `Holds` means that some stored
    row has a value of `e` that equals `x` under the comparison of `IN`, proved with the lemmas and `sql_simp`,
    with instances on one database where `decide +kernel` checks the claim for a true and for a false `x`."""
    result = run_command(surface_command(runtime_root, FIXTURES / "ClaimsIn.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()
