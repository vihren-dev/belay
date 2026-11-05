"""The row of a group of an aggregate query in the public Lean surface (ADR 0030, D5)."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_row_of_a_group_in_the_kernel(runtime_root: Path, tmp_path: Path) -> None:
    """`GroupRow.lean` and `Resolution/GroupAssociation.lean`: kernel-checked queries read the row of the
    maximum, the row of the last distinct call, and the first row for an associated expression column; the
    general law gives the first row without a deciding call. No proof uses an unchecked axiom."""
    result = run_command(surface_command(runtime_root, FIXTURES / "ClaimsGroupValues.lean", tmp_path),
                         cwd=tmp_path, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    reports = [line for line in result.stdout.splitlines() if "depends on axioms" in line]
    assert len(reports) == 5, result.stdout
    assert all(name not in result.stdout for name in ("sorryAx", "ofReduceBool", "_native")), result.stdout
