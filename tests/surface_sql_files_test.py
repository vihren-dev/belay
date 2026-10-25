"""S7 file construction shares inline parameter semantics and finds the owning package."""

import json
import os
from pathlib import Path
import shutil

import pytest

from tests.runtime_support import run_command
from tests.sql_file_support import installed_layout, lake_build, write_package
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_file_parameter_construction_and_replay(runtime_root: Path, tmp_path: Path) -> None:
    """SqlFileTerm preserves explicit dollar arguments, sparse slots and S5's validated source hints."""
    result = run_command(surface_command(runtime_root, FIXTURES / "SqlFileConstruction.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    assert "file construction and replay passed" in result.stdout, result.diagnostic()


@pytest.mark.parametrize(("text", "message"), [
    ("SELECT :id, $id", "both give the Lean name id"),
    ("SELECT $x, ?1", "one number, 1"),
    ("SELECT $a::b", "cannot name a Lean argument"),
])
def test_file_parameter_diagnostics(runtime_root: Path, tmp_path: Path, text: str, message: str) -> None:
    """The common planner retains identity conflicts and reports their external SQL location."""
    header = (FIXTURES / "SqlFileConstruction.lean").read_text().split("/-- The file's dollar")[0]
    source = tmp_path / "FileError.lean"
    source.write_text(header + f"\ndef bad := file_parameters {json.dumps(text)}\n")
    result = run_command(surface_command(runtime_root, source, tmp_path), cwd=tmp_path, timeout=60)
    assert result.returncode == 1, result.diagnostic()
    assert "sql/queries.sql:1:" in result.stdout and message in result.stdout, result.diagnostic()
    assert result.stdout.count(": error:") == 1, result.diagnostic()


def test_sql_file_uses_owning_package(runtime_root: Path, tmp_path: Path) -> None:
    """SqlFileSource reads nested dependency sources from their package, including after relocation."""
    installed = installed_layout(runtime_root, tmp_path)
    dependency = tmp_path / "dependency"
    write_package(dependency, "SqlDependency", installed)
    (dependency / "sql/query.sql").write_text("SELECT $x, 7")
    nested = dependency / "lean/SqlDependency"
    nested.mkdir()
    (nested / "lakefile.toml").write_text('name = "Unrelated"\n')
    (nested / "lake-manifest.json").write_text(json.dumps({"name": "Unrelated", "packages": []}))
    (nested / "sql").mkdir()
    (nested / "sql/query.sql").write_text("SELECT $x, 99")
    probe = (FIXTURES / "SqlFileProbe.lean").read_text()
    (nested / "Queries.lean").write_text(probe + '\nnamespace SqlDependency\ndef query := file_probe "sql/query.sql"\n'
                                       'example (x : Value) : query x = sql "SELECT $x, 7" := rfl\nend SqlDependency\n')
    (dependency / "lean/SqlDependency.lean").write_text("import SqlDependency.Queries\n")
    consumer = tmp_path / "consumer"
    write_package(consumer, "Consumer", installed,
                  '\n[[require]]\nname = "SqlAlias"\npath = "../dependency"\n')
    (consumer / "sql/query.sql").write_text("SELECT $x, 8")
    (consumer / "lean/Consumer.lean").write_text(
        'import SqlDependency\nopen Belay.Sqlite\n'
        '\ndef query := file_probe "sql/query.sql"\n'
        'example (x : Value) : query x = sql "SELECT $x, 8" := rfl\n'
        'example (x : Value) : SqlDependency.query x = sql "SELECT $x, 7" := rfl\n')
    toolchain = runtime_root / "lean/bin"
    result = lake_build(installed, consumer, "Consumer")
    assert result.returncode == 0, result.diagnostic()
    assert not (dependency / "lake-manifest.json").exists()
    setup = dependency / ".lake/build/ir/SqlDependency/Queries.setup.json"
    assert json.loads(setup.read_text())["package"] == "SqlDependency"
    # Reuse Lake's real compiler setup from another process directory, as an editor can.
    result = run_command([str(toolchain / "lean"), f"--setup={setup}", str(nested / "Queries.lean")],
                         cwd=tmp_path, timeout=60, environment={"PATH": str(toolchain),
                         "LEAN_SRC_PATH": os.pathsep.join(map(str, [consumer / "lean", dependency / "lean"]))})
    assert result.returncode == 0, result.diagnostic()
    relocated = tmp_path / "relocated"
    shutil.copytree(dependency, relocated, ignore=shutil.ignore_patterns(".lake", "lake-manifest.json"))
    result = lake_build(installed, relocated, "SqlDependency")
    assert result.returncode == 0, result.diagnostic()


@pytest.mark.parametrize(("configured", "package", "message"), [
    (False, True, "cannot find the package"),
    (True, True, "cannot read SQL file sql/missing.sql"),
    (True, False, "need the owning package's module setup"),
])
def test_sql_file_load_errors(runtime_root: Path, tmp_path: Path, configured: bool,
                             package: bool, message: str) -> None:
    """SqlFileSource reports unavailable roots, unreadable sources and absent compiler identity."""
    if configured:
        (tmp_path / "lakefile.toml").write_text('name = "fixture"\n')
        (tmp_path / "lake-manifest.json").write_text(json.dumps({"name": "fixture", "packages": []}))
    source = tmp_path / "Missing.lean"
    source.write_text((FIXTURES / "SqlFileProbe.lean").read_text() +
                      '\ndef query := file_probe "sql/missing.sql"\n')
    command = surface_command(runtime_root, source, tmp_path)
    setup_path = tmp_path / "setup.json"
    setup = json.loads(setup_path.read_text())
    if package:
        setup["package"] = "fixture"
    setup_path.write_text(json.dumps(setup))
    result = run_command(command, cwd=tmp_path, timeout=60)
    assert result.returncode == 1, result.diagnostic()
    assert message in result.stdout and result.stdout.count(": error:") == 1, result.diagnostic()
    if message.startswith("cannot read"):
        assert "the file exists and is readable" in result.stdout, result.diagnostic()
    if message.startswith("cannot find"):
        assert "set belay.sql.packageRoot" in result.stdout, result.diagnostic()
