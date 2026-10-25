"""The checked SQL observation primitive of the documentation blocks uses installed surface code."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, module_setup

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_sql_doc_observations(runtime_root: Path, tmp_path: Path) -> None:
    """Our checker retains exact typed outputs, all alternatives and whitespace, and its
    actual-run adapter uses bindings, fresh databases and explicit clock environments."""
    setup = module_setup(runtime_root, tmp_path)
    result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup}",
                          str(FIXTURES / "SqlDocObservation.lean")], cwd=tmp_path, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    assert "SQL doc observation checks passed" in result.stdout, result.diagnostic()


@pytest.mark.parametrize(("fixture", "message"), [
    ("SqlDocComments", "SQL doc comment checks passed"),
    ("SqlDocSource", "SQL doc source checks passed"),
    ("SqlDocBindings", "SQL doc binding checks passed"),
])
def test_sql_doc_pure_helpers(runtime_root: Path, tmp_path: Path, fixture: str, message: str) -> None:
    """The `#guard` checks of a fixture hold for the helper that it names, in `SqlDocComments` (the
    lexical expected-text reader), `SqlDocSource` (the map from an indented fence to the original
    file) or `SqlDocBindings` (the parameter plans and their problems)."""
    setup = module_setup(runtime_root, tmp_path)
    result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup}",
                          str(FIXTURES / f"{fixture}.lean")], cwd=tmp_path, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    assert message in result.stdout, result.diagnostic()
