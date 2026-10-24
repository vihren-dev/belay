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
