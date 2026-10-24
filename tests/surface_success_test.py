"""S4 program composition and success contracts in the public Lean surface."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_program_laws_preserve_connection_and_next_index(runtime_root: Path, tmp_path: Path) -> None:
    """ProgramMonadLaws and ProgramBindLaws compose arbitrary programs, preserve transactions,
    advance a statement-dependent clock, and stop before the next program after an unmodeled step.
    The law wrappers use no unchecked reduction axiom."""
    result = run_command(surface_command(runtime_root, FIXTURES / "SuccessProgramLaws.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    reports = [line for line in result.stdout.splitlines() if "depends on axioms" in line]
    assert len(reports) == 3, result.stdout
    assert all(name not in result.stdout for name in ("sorryAx", "ofReduceBool", "_native")), result.stdout
