"""Kernel consumers of stored-view expansion through the public SQL surface."""

import json
from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, module_setup

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


@pytest.mark.parametrize("fixture", ["ClaimsViews", "ClaimsViewScope", "ClaimsViewTriggers"])
def test_stored_views_use_the_indexed_query_resolver(runtime_root: Path, tmp_path: Path, fixture: str) -> None:
    """QuerySourceExpansion preserves late lookup, metadata, closed names and trigger-cell
    offsets; every concrete validity and query assertion is checked by Lean's kernel."""
    setup_path = module_setup(runtime_root, tmp_path)
    setup = json.loads(setup_path.read_text())
    for name in ("ViewsSupport", fixture):
        setup["name"] = name
        setup_path.write_text(json.dumps(setup))
        artifact = tmp_path / f"{name}.olean"
        result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup_path}",
                              "-o", str(artifact), str(FIXTURES / f"{name}.lean")],
                             cwd=tmp_path, timeout=90)
        assert result.returncode == 0, result.diagnostic()
        assert all(term not in result.stdout for term in ("sorryAx", "ofReduceBool", "_native")), result.stdout
        setup["importArts"][name] = [[str(artifact)]]
