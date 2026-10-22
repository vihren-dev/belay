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


def test_guide_scripts_examples_hold(runtime_root: Path, tmp_path: Path) -> None:
    """The section "Scripts" (`Belay/Sqlite/Script.lean`, `Belay/Sqlite/SqlTerm.lean`): `sql r"..."`
    gives the statements of the text in order, in plain and `#` raw strings, and `++` with
    `Script.empty` is a monoid."""
    result = run_command(surface_command(runtime_root, FIXTURES / "GuideScripts.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_sql_errors_are_at_their_position_in_the_text(runtime_root: Path, tmp_path: Path) -> None:
    """`sql r"..."` (`Belay/Sqlite/SqlTerm.lean`, `textRange` of `Belay/Sqlite/SqlLiteral.lean`) is an
    elaboration error at the byte of the SQL text where SQLite's grammar rejects it, in a plain raw
    string and in raw strings with one and three `#`, and at the statement that the translation
    refuses, with its message."""
    result = run_command(surface_command(runtime_root, FIXTURES / "ScriptErrors.lean", tmp_path), cwd=tmp_path,
                         timeout=60)
    assert result.returncode == 1, result.diagnostic()
    for position in ("11:42", "12:49", "13:49"):
        assert f"ScriptErrors.lean:{position}: error: SQLite's grammar rejects the SQL at this offset" in \
            result.stdout, result.diagnostic()
    assert "ScriptErrors.lean:14:30: error: This statement is not modeled" in result.stdout, result.diagnostic()
