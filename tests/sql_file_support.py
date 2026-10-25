"""Fixture packages for the SQL-file tests: a real Lake consumer of the installed Belay package.

The surface runtime root holds installed packages. Lake resolves a path requirement relative to
the requiring package, so the fixture mirrors the installed sibling layout with real directories
and linked entries, and gives Lake the parser library that the producer's build used."""

import json
import os
from pathlib import Path

from tests.runtime_support import CommandResult, run_command
from tests.surface_support import FIXTURES, surface_command

PROBE = (FIXTURES / "SqlFileProbe.lean").read_text()
"""The probe module that exposes `file_probe`, a form that reads an SQL file through `loadSqlFileSource`."""
OUTER_SQL, NESTED_SQL = "SELECT $x, 7", "SELECT $x, 99"
"""The texts of `sql/query.sql` in the outer package and in its nested project of the same name."""


def installed_layout(runtime_root: Path, tmp_path: Path) -> Path:
    """Mirror the installed packages below `tmp_path` so that `../` requirements keep their layout."""
    installed = tmp_path / "installed"
    (installed / "packages").mkdir(parents=True)
    (installed / "lean").symlink_to(runtime_root / "lean", target_is_directory=True)
    for package in (runtime_root / "packages").iterdir():
        folder = installed / "packages" / package.name
        folder.mkdir()
        for entry in package.iterdir():
            (folder / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
    return installed


def write_package(folder: Path, name: str, installed: Path, extra: str = "") -> None:
    """Create a package that requires the installed Belay package without fetching anything."""
    folder.mkdir(parents=True)
    (folder / "lakefile.toml").write_text(
        f'name = "{name}"\n\n[[require]]\nname = "belay"\n'
        f'path = {json.dumps(str(installed / "packages/belay"))}\n{extra}\n'
        f'[[lean_lib]]\nname = "{name}"\nsrcDir = "lean"\n')
    (folder / "lean-toolchain").write_text((installed / "packages/belay/lean-toolchain").read_text())
    (folder / "lean").mkdir()
    (folder / "sql").mkdir()


def toolchain_environment(installed: Path) -> dict[str, str]:
    """The environment of a Lake process: the installed toolchain and the producer's parser library."""
    return {"PATH": str(installed / "lean/bin"), "BELAY_PARSER_LIBRARY": os.environ["BELAY_PARSER_LIBRARY"]}


def lake_build(installed: Path, package: Path, target: str) -> CommandResult:
    """Build `target` in `package` with the installed Lake, with a finite timeout."""
    return run_command([str(installed / "lean/bin/lake"), "build", "--no-ansi", target], cwd=package,
                       timeout=180, environment=toolchain_environment(installed))


def configured_command(runtime_root: Path, source: Path, directory: Path) -> list[str]:
    """The surface command with a package identity but no Lake workspace, so only the option can locate SQL."""
    command = surface_command(runtime_root, source, directory)
    setup_path = directory / "setup.json"
    setup = json.loads(setup_path.read_text())
    setup["package"] = "fixture"
    setup_path.write_text(json.dumps(setup))
    return command


def write_lean_package(folder: Path, name: str, installed: Path, libraries: list[str], inputs: str = "",
                       needs: str = "") -> None:
    """Create a package with a `lakefile.lean`, so that it can declare `input_dir` inputs and library `needs`.

    Each library has its root module in `lean/<library>.lean`."""
    folder.mkdir(parents=True)
    body = (f'import Lake\nopen Lake DSL\n\npackage {name}\n\nrequire belay from {json.dumps(str(installed / "packages/belay"))}\n'
            f'\n{inputs}\n')
    for library in libraries:
        body += f'\nlean_lib {library} where\n  srcDir := "lean"\n  roots := #[`{library}]\n{needs}\n'
    (folder / "lakefile.lean").write_text(body)
    (folder / "lean-toolchain").write_text((installed / "packages/belay/lean-toolchain").read_text())
    (folder / "lean").mkdir()
    (folder / "sql").mkdir()


def run_checker(installed: Path, package: Path, *arguments: str) -> CommandResult:
    """Run the installed `belay-sql-check` through `lake exe` in `package`, with a finite timeout."""
    return run_command([str(installed / "lean/bin/lake"), "exe", "--no-ansi", "belay-sql-check", *arguments],
                       cwd=package, timeout=120, environment=toolchain_environment(installed))


def write_same_name_projects(world: Path, installed: Path, with_option: bool) -> None:
    """A dependency whose nested Lake project has the same package name, so discovery sees two roots."""
    dependency = world / "dependency"
    write_package(dependency, "Twin", installed)
    (dependency / "sql/query.sql").write_text(OUTER_SQL)
    nested = dependency / "lean"
    (nested / "sql").mkdir()
    (nested / "sql/query.sql").write_text(NESTED_SQL)
    (nested / "lakefile.toml").write_text('name = "Twin"\n')
    (nested / "lake-manifest.json").write_text(json.dumps({"name": "Twin", "packages": []}))
    body = PROBE + "\n"
    if with_option:
        body += ('set_option belay.sql.packageRoot ".." in\ndef outer := file_probe "sql/query.sql"\n'
                 'set_option belay.sql.packageRoot "." in\ndef inner := file_probe "sql/query.sql"\n'
                 'example (x : Value) : outer x = sql "SELECT $x, 7" := rfl\n'
                 'example (x : Value) : inner x = sql "SELECT $x, 99" := rfl\n')
    else:
        body += 'def outer := file_probe "sql/query.sql"\n'
    (nested / "Twin.lean").write_text(body)
    consumer = world / "consumer"
    write_package(consumer, "Consumer", installed, '\n[[require]]\nname = "Twin"\npath = "../dependency"\n')
    (consumer / "lean/Consumer.lean").write_text("import Twin\n")
