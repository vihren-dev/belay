"""`build-support/library_lakefile.py`: the installed runtime's lakefile (ADR 0010 section 3)."""

import importlib.util
from pathlib import Path
import tomllib
from types import ModuleType

import pytest

pytestmark = pytest.mark.unit

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "packages/sqlite-verifier/lakefile.toml"
"""The verifier library package's lakefile, which the runtime build reads."""


def generator() -> ModuleType:
    """Load the build script, which is not in a package."""
    specification = importlib.util.spec_from_file_location("library_lakefile", ROOT / "build-support/library_lakefile.py")
    assert specification is not None and specification.loader is not None
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


def test_runtime_lakefile_keeps_libraries_and_moves_requirements() -> None:
    """`library_lakefile` keeps the package's library declarations exactly, points the model package to its
    folder in the runtime, and turns the artifact cache off for read-only outputs."""
    package = tomllib.loads(PACKAGE.read_text())
    result = tomllib.loads(generator().library_lakefile(package))
    assert result["lean_lib"] == package["lean_lib"]
    assert result["require"] == [{"name": "belaySqlite", "path": "packages/belay-sqlite"}]
    assert result["enableArtifactCache"] is False
    assert (result["name"], result["version"]) == (package["name"], package["version"])


@pytest.mark.parametrize("addition", ['[[require]]\nname = "lean4export"\npath = "../x"\n',
                                      '[[lean_exe]]\nname = "tool"\nroot = "Tool"\n'])
def test_part_the_runtime_does_not_ship_is_refused(addition: str) -> None:
    """`library_lakefile` refuses a requirement or an executable that the runtime does not ship, because the
    runtime's lakefile would then name a missing folder or target."""
    package = tomllib.loads(PACKAGE.read_text() + "\n" + addition)
    with pytest.raises(SystemExit, match="installed runtime does not ship"):
        generator().library_lakefile(package)
