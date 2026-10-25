"""S7 package-root override: automatic discovery stays, and `belay.sql.packageRoot` resolves ambiguity."""

import json
import os
from pathlib import Path
import shutil

import pytest

from tests.runtime_support import run_command
from tests.sql_file_support import (OUTER_SQL, PROBE, configured_command, installed_layout, lake_build,
                                    write_same_name_projects)
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]



def test_explicit_root_primitive(runtime_root: Path, tmp_path: Path) -> None:
    """readSqlFileSourceAtRoot keeps text and relative identity and rejects unsafe roots and paths."""
    result = run_command(surface_command(runtime_root, FIXTURES / "SqlFileRoot.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    assert "explicit root checks passed" in result.stdout, result.diagnostic()


def test_option_root_is_anchored_at_the_lean_file(runtime_root: Path, tmp_path: Path) -> None:
    """An option root needs no manifest and ignores the compiler's working directory."""
    project = tmp_path / "project"
    (project / "sql").mkdir(parents=True)
    (project / "sql/q.sql").write_text(OUTER_SQL)
    (project / "lean").mkdir()
    source = project / "lean/Q.lean"
    source.write_text(PROBE + '\nset_option belay.sql.packageRoot ".." in\ndef query := file_probe "sql/q.sql"\n'
                      'example (x : Value) : query x = sql "SELECT $x, 7" := rfl\n')
    elsewhere = tmp_path / "elsewhere"
    elsewhere.mkdir()
    result = run_command(configured_command(runtime_root, source, elsewhere), cwd=elsewhere, timeout=60)
    assert result.returncode == 0, result.diagnostic()


@pytest.mark.parametrize(("root", "message"), [
    ("/", "is absolute; use a path relative to the Lean file's directory"),
    ("missing", "not a directory; set it to an existing directory, written relative to the Lean file's directory"),
    ("Q.lean", "not a directory; set it to an existing directory, written relative to the Lean file's directory"),
])
def test_invalid_option_roots_report_one_error(runtime_root: Path, tmp_path: Path, root: str, message: str) -> None:
    """Absolute, missing and non-directory roots fail at the form with the option's name."""
    source = tmp_path / "Q.lean"
    source.write_text(PROBE + f'\nset_option belay.sql.packageRoot {json.dumps(root)} in\n'
                      'def query := file_probe "sql/q.sql"\n')
    result = run_command(configured_command(runtime_root, source, tmp_path), cwd=tmp_path, timeout=60)
    assert result.returncode == 1, result.diagnostic()
    assert "belay.sql.packageRoot" in result.stdout and message in result.stdout, result.diagnostic()
    assert result.stdout.count(": error:") == 1, result.diagnostic()


def test_same_name_projects_need_and_accept_the_override(runtime_root: Path, tmp_path: Path) -> None:
    """Discovery refuses to guess between two valid roots; the option selects either, also after relocation."""
    installed = installed_layout(runtime_root, tmp_path)
    ambiguous = tmp_path / "ambiguous"
    write_same_name_projects(ambiguous, installed, with_option=False)
    result = lake_build(installed, ambiguous / "consumer", "Consumer")
    assert result.returncode != 0 and "ambiguous package roots" in result.stdout + result.stderr, result.diagnostic()
    assert "belay.sql.packageRoot" in result.stdout + result.stderr, result.diagnostic()
    world = tmp_path / "world"
    write_same_name_projects(world, installed, with_option=True)
    result = lake_build(installed, world / "consumer", "Consumer")
    assert result.returncode == 0, result.diagnostic()
    # An editor compiles with Lake's setup from another working directory; the option still anchors at the file.
    setup = world / "dependency/.lake/build/ir/Twin.setup.json"
    elsewhere = tmp_path / "elsewhere"
    elsewhere.mkdir()
    toolchain = installed / "lean/bin"
    result = run_command([str(toolchain / "lean"), f"--setup={setup}", str(world / "dependency/lean/Twin.lean")],
                         cwd=elsewhere, timeout=60, environment={"PATH": str(toolchain),
                         "LEAN_SRC_PATH": os.pathsep.join(map(str, [world / "consumer/lean", world / "dependency/lean"]))})
    assert result.returncode == 0, result.diagnostic()
    moved = tmp_path / "moved"
    shutil.copytree(world, moved, ignore=shutil.ignore_patterns(".lake", "lake-manifest.json"), symlinks=True)
    (moved / "dependency/lean/lake-manifest.json").write_text(json.dumps({"name": "Twin", "packages": []}))
    result = lake_build(installed, moved / "consumer", "Consumer")
    assert result.returncode == 0, result.diagnostic()
