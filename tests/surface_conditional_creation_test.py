"""IF NOT EXISTS on CREATE TABLE and CREATE INDEX in the public Lean surface (ADR 0030, D3)."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import fixture_file, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_conditional_creation_keeps_the_database_or_creates(runtime_root: Path, tmp_path: Path) -> None:
    """`{Queries/Preparation,Schema/Ddl}/ConditionalCreation.lean`, `ConditionalCreationSteps.lean` and the generalised
    `Script.createIndex_allOk_iff`: kernel-checked no-ops keep the database, the counters and a
    rollback; the checks before the name check keep their errors; the general laws give the no-op
    step and the step with a free name. No proof uses an unchecked axiom."""
    result = run_command(surface_command(runtime_root, fixture_file("ClaimsConditionalCreation.lean"), tmp_path),
                         cwd=tmp_path, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    reports = [line for line in result.stdout.splitlines() if "depends on axioms" in line]
    assert len(reports) == 9, result.stdout
    assert all(name not in result.stdout for name in ("sorryAx", "ofReduceBool", "_native")), result.stdout
