"""Fixture packages for the SQL-file tests: a real Lake consumer of the installed Belay package.

The surface runtime root holds installed packages. Lake resolves a path requirement relative to
the requiring package, so the fixture mirrors the installed sibling layout with real directories
and linked entries, and gives Lake the parser library that the producer's build used."""

import json
import os
from pathlib import Path

from tests.runtime_support import CommandResult, run_command
from tests.surface_support import surface_command


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
