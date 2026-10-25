"""S7 `sql_file` and `sql_module`: the same scripts as inline SQL, and one clear error for each refusal."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.sql_file_support import configured_command
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

PREAMBLE = ('import Belay\nimport Belay.Sqlite.SqlModule\nimport Belay.Sqlite.SqlFileSyntax\n'
            'open Belay.Sqlite\nset_option belay.sql.packageRoot "."\n'
            'def shop : Database := db! r"CREATE TABLE t(x INTEGER);"\n')


def test_file_and_module_forms_equal_inline_sql(runtime_root: Path, tmp_path: Path) -> None:
    """Files, sections, `against` and modules elaborate to the scripts and documentation that the fixture states."""
    result = run_command(configured_command(runtime_root, FIXTURES / "SqlFileForms.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    assert "module forms passed" in result.stdout, result.diagnostic()


def test_pure_file_layout_checks(runtime_root: Path, tmp_path: Path) -> None:
    """Comments, markers, names and tool-syntax hints over small texts, as `#guard` in the fixture."""
    result = run_command(surface_command(runtime_root, FIXTURES / "SqlFileLayoutChecks.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_refused_forms_give_exactly_one_located_error(runtime_root: Path, tmp_path: Path) -> None:
    """Each refusal in the fixture is checked with `#guard_msgs`, which also rejects any extra message."""
    result = run_command(configured_command(runtime_root, FIXTURES / "SqlFileErrors.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()


@pytest.mark.parametrize(("text", "form", "position"), [
    ("-- é😀\r\nSELECT x FROM t;\r\nSELECT é😀;\r\n", 'sql_file "q.sql" (against := shop)', "q.sql:3:8: "),
    ("-- é😀\r\nSELECT 1;\r\n  .mode csv\r\n", 'sql_file "q.sql"', "q.sql:3:3: "),
    ("-- name: a\r\nSELECT 1;\r\n-- name: a\r\nSELECT 2;\r\n", 'sql_module Q from "q.sql"', "q.sql:3:1: "),
])
def test_positions_are_characters_of_the_original_file(runtime_root: Path, tmp_path: Path, text: str,
                                                      form: str, position: str) -> None:
    """Unicode, a character outside the BMP and CRLF line ends do not move the reported line or column."""
    (tmp_path / "q.sql").write_bytes(text.encode())
    body = form if form.startswith("sql_module") else f"def q := {form}"
    source = tmp_path / "Q.lean"
    source.write_text(PREAMBLE + body + "\n")
    result = run_command(configured_command(runtime_root, source, tmp_path), cwd=tmp_path, timeout=60)
    assert result.returncode == 1, result.diagnostic()
    assert position in result.stdout, result.diagnostic()
    assert result.stdout.count(": error:") == 1, result.diagnostic()
