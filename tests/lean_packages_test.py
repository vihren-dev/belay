"""Each Lean package derivation's output replays in a workspace that requires it (ADR 0010 section 7).

`build-support/lean-package.nix` builds each package under `packages/` once, and its
output is the package's Lake workspace. The runtime, the API reference and the next
package's build require these outputs. If an output misses a file that Lake needs,
Lake compiles the package's modules again in each of them, or fails on the read-only
store. The runtime root of this suite holds the outputs in the repository layout.
"""

import json
from pathlib import Path
import re
import tomllib

import pytest

from tests.runtime_support import run_command

pytestmark = [pytest.mark.integration, pytest.mark.environment]

BUILT_MODULE = re.compile(r"Built (\S+)")
"""A Lake progress line for a target that Lake compiled, not replayed (as `lake_workspace.BUILT_MODULE`)."""

TIMEOUT_SECONDS = 120
"""Deadline for one replay; replaying a package takes less than a second."""

MODEL_PACKAGE = "belaySqliteModel"
"""The producer whose native facets text and surface builds consume; other packages supply binaries."""


def pytest_generate_tests(metafunc: pytest.Metafunc) -> None:
    """One check for each package folder of the runtime under test, so a new package needs no new test."""
    if "package" in metafunc.fixturenames:
        root = metafunc.config.getoption("runtime_root") or metafunc.config.rootpath
        metafunc.parametrize("package", sorted(path.name for path in (root / "packages").iterdir()))


def replay_targets(lakefile: dict[str, object]) -> list[str]:
    """Libraries, executable root modules, and the model's native library facets.

    Text and surface builds need the model's native objects and shared libraries.
    Replaying those facets detects the producer omission that made each consumer
    compile the model again. Other executable packages supply finished binaries;
    their root-module replay does not request another executable link.
    """
    libraries = [f"{lakefile['name']}/{library['name']}" for library in lakefile.get("lean_lib", [])]
    native = [f"{library}:shared" for library in libraries] if lakefile["name"] == MODEL_PACKAGE else []
    executables = [f"+{executable.get('root', executable['name'])}" for executable in lakefile.get("lean_exe", [])]
    return [*libraries, *native, *executables]


def test_package_output_compiles_nothing(package: str, runtime_root: Path, tmp_path: Path) -> None:
    """The installed package replays its modules and required model native facets without compiling."""
    folder = runtime_root / "packages" / package
    lakefile = tomllib.loads((folder / "lakefile.toml").read_text())
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    (workspace / "lakefile.toml").write_text(f'name = "replayCheck"\n\n[[require]]\nname = {json.dumps(lakefile["name"])}\n'
                                            f'path = {json.dumps(str(folder))}\n')
    (workspace / "lean-toolchain").write_text((folder / "lean-toolchain").read_text())
    toolchain = runtime_root / "lean/bin"
    result = run_command([str(toolchain / "lake"), "build", "--no-ansi", *replay_targets(lakefile)], cwd=workspace,
                         timeout=TIMEOUT_SECONDS, environment={"HOME": str(tmp_path), "PATH": str(toolchain)})
    assert result.returncode == 0, result.diagnostic()
    assert BUILT_MODULE.findall(result.stdout) == [], (
        f"Lake compiled modules of {package}; its derivation output misses files that Lake needs:\n"
        + result.diagnostic())
