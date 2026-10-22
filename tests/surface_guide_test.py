"""The examples of the user guide in the product repository, as the guide writes them, over the
surface (`packages/belay`, ADR 0017, D3). Each fixture holds the examples of one section and fails
to elaborate when an example does not hold.
"""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_guide_values_examples_hold(runtime_root: Path, tmp_path: Path) -> None:
    """The section "Values" (`Belay/Sqlite/Values.lean`): the literal coercions, the order of
    `Value.compare`, three-valued truth, `Value.store` and the named lemmas."""
    result = run_command(surface_command(runtime_root, FIXTURES / "GuideValues.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_guide_databases_examples_hold(runtime_root: Path, tmp_path: Path) -> None:
    """The section "Databases" (`Belay/Sqlite/Database.lean`): `Database.empty`, `db.rows`, and the
    facts of a valid database, which need no hypothesis."""
    result = run_command(surface_command(runtime_root, FIXTURES / "GuideDatabases.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()
