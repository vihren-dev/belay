"""S5 SQL name/value inference feeds the shared certified-candidate boundary."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_sql_names_and_bindings_supply_certifiable_samples(runtime_root: Path, tmp_path: Path) -> None:
    """Our hints retain aliases, quoted names and bindings, and their candidate certifies the
    intended NOCASE data failure under explicit catalog/row premises."""
    result = run_command(surface_command(runtime_root, FIXTURES / "CounterexampleInference.lean", tmp_path),
                         cwd=tmp_path, timeout=90)
    assert result.returncode == 0, result.diagnostic()
    assert "inferred SQL counterexample certified" in result.stdout, result.stdout
    assert "sorry" not in result.stdout, result.stdout
