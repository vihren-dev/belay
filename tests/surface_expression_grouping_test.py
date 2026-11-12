"""Grouping terms that are expressions in the public Lean surface (ADR 0030, D4)."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import fixture_file, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_expression_grouping_in_the_kernel(runtime_root: Path, tmp_path: Path) -> None:
    """`resolveGroupTermTraced` and `resolveGroupExpressionTraced` of `Queries/Select/QueryAggregates.lean`:
    kernel-checked queries group by an expression without affinity and under its collation, read a number
    as a result column or a constant, and refuse an alias inside a term and a subquery. No proof uses an
    unchecked axiom."""
    result = run_command(surface_command(runtime_root, fixture_file("ClaimsExpressionGrouping.lean"), tmp_path),
                         cwd=tmp_path, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    reports = [line for line in result.stdout.splitlines() if "depends on axioms" in line]
    assert len(reports) == 4, result.stdout
    assert all(name not in result.stdout for name in ("sorryAx", "ofReduceBool", "_native")), result.stdout
