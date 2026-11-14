"""The top-level package `belay` (`lakefile.toml`, `lake-manifest.json` and `BelayRoot.lean` in the top-level
folder): the package that users require from the repository root, with no `subDir`. It requires the surface
package `belaySurface` in `packages/belay`.

The Nix sandbox has no network, so a consumer requires the root by path. A `git` requirement on the root differs
only in the folder that Lake clones the repository into.
"""

import json
from pathlib import Path
import shutil

import pytest

from tests.runtime_support import CommandResult, run_command
from tests.sql_file_support import installed_layout, lake_build, run_checker, toolchain_environment

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

ROOT_FILES = ("lakefile.toml", "lean-toolchain", "BelayRoot.lean")
"""The files of the top-level package that the layout copies unchanged; the manifest is written separately."""
PLAUSIBLE_FOLDER = "packages/belay/.lake/packages/plausible"
"""The folder of Plausible in the surface's Nix output, which requires it by this path (`build-support/default.nix`)."""
CLAIM = '''import Belay
open Belay.Sqlite

/-- A schema with one table. -/
def notes : Database := db! r"CREATE TABLE notes (id INTEGER PRIMARY KEY, body TEXT NOT NULL);"

/-- A migration that deletes every row, so it does not keep the read below. -/
def clearNotes : Script := sql r"DELETE FROM notes"

/-- The read that the migration must keep, from an SQL file of the package. -/
def allNotes : Script := sql_file "sql/all_notes.sql"

#sql_check clearNotes preserves allNotes on notes
'''
"""A consumer module with a `db!` schema, an `sql` script, an `sql_file` read and a `#sql_check` whose answer is
`false`."""


def root_layout(runtime_root: Path, tmp_path: Path) -> Path:
    """The installed packages of `installed_layout` with the files of the top-level package at their paths.

    The root manifest pins Plausible as a `git` package. The copy pins it by the path of the surface's Nix
    output, because the test has no network; the other entries stay as they are."""
    installed = installed_layout(runtime_root, tmp_path)
    for name in ROOT_FILES:
        shutil.copy(runtime_root / name, installed / name)
    manifest = json.loads((runtime_root / "lake-manifest.json").read_text())
    entries = []
    for entry in manifest["packages"]:
        if entry["name"] == "plausible":
            assert entry["type"] == "git", entry
            entry = {key: entry[key] for key in ("name", "scope", "inherited", "manifestFile", "configFile")}
            entry |= {"type": "path", "dir": PLAUSIBLE_FOLDER}
        entries.append(entry)
    (installed / "lake-manifest.json").write_text(json.dumps(manifest | {"packages": entries}))
    return installed


def write_consumer(folder: Path, requirement: str, installed: Path) -> None:
    """A package `Consumer` with the library `Consumer`, the module `CLAIM` and its SQL file, that requires
    the package at `requirement` below `installed` under its own name."""
    name = "belay" if requirement == "." else "belaySurface"
    folder.mkdir(parents=True)
    (folder / "lakefile.toml").write_text(
        f'name = "Consumer"\n\n[[require]]\nname = "{name}"\npath = {json.dumps(str(installed / requirement))}\n'
        '\n[[lean_lib]]\nname = "Consumer"\n')
    (folder / "lean-toolchain").write_text((installed / "lean-toolchain").read_text())
    (folder / "Consumer.lean").write_text(CLAIM)
    (folder / "sql").mkdir()
    (folder / "sql/all_notes.sql").write_text("SELECT id, body FROM notes")


def check_block(result: CommandResult) -> str:
    """The output of `#sql_check` in a Lake build of the module `Consumer`, without the file positions."""
    assert result.returncode == 0, result.diagnostic()
    lines = result.stdout.splitlines()
    start = next(index for index, line in enumerate(lines) if "SQL check:" in line)
    return "\n".join([lines[start].split("SQL check:", 1)[1], *lines[start + 1:]])


@pytest.mark.timeout(300)
def test_a_root_requirement_checks_and_reports_as_a_surface_requirement(runtime_root: Path, tmp_path: Path) -> None:
    """The root `lakefile.toml` and `lake-manifest.json`: a project that requires `belay` from the repository root
    compiles a module with `db!`, `sql`, `sql_file` and `#sql_check`, whose answer is `false` and is the same as in
    a project that requires `packages/belay`. `lake exe belay-sql-check` finds the checker through the root package
    and gives the same report: `packagesNamed` and `sqlPackageRoot` find the consumer's SQL file with the root
    package in the workspace."""
    installed = root_layout(runtime_root, tmp_path)
    answers, reports = [], []
    for requirement in (".", "packages/belay"):
        consumer = tmp_path / ("root" if requirement == "." else "surface") / "consumer"
        write_consumer(consumer, requirement, installed)
        answers.append(check_block(lake_build(installed, consumer, "Consumer")))
        report = run_checker(installed, consumer)
        assert report.returncode == 0, report.diagnostic()
        reports.append(report.stdout)
    assert answers[0].startswith(" false.\nDatabase:\nnotes:\n  id | body\n  1  | ''\n"), answers[0]
    assert answers[0] == answers[1]
    assert reports[0] == reports[1] == "library Consumer: 1 modules, 1 SQL sources, 0 stale\n", reports


@pytest.mark.timeout(300)
def test_lake_build_in_the_root_builds_the_library(runtime_root: Path, tmp_path: Path) -> None:
    """The default target of the root `lakefile.toml`, the module `BelayRoot`: `lake build` with no target in the
    top-level folder succeeds without a warning and loads the shared library of `Belay` for the module, so a
    build of the root package, as Reservoir runs it, builds the library and its shared library."""
    installed = root_layout(runtime_root, tmp_path)
    result = run_command([str(installed / "lean/bin/lake"), "build", "--no-ansi"], cwd=installed, timeout=280,
                         environment=toolchain_environment(installed))
    assert result.returncode == 0, result.diagnostic()
    assert "warning" not in (result.stdout + result.stderr).lower(), result.diagnostic()
    setup = json.loads((installed / ".lake/build/ir/BelayRoot.setup.json").read_text())
    shared = [Path(path) for path in setup["dynlibs"] if Path(path).name.startswith("libbelaySurface_Belay.")]
    assert len(shared) == 1 and shared[0].is_file(), setup["dynlibs"]
