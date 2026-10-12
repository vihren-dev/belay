"""`build-support/library_lakefile.py`: the installed runtime's library-only lakefile (ADR 0010 section 3)."""

import importlib.util
from pathlib import Path
import tomllib
from types import ModuleType

import pytest

pytestmark = pytest.mark.unit

ROOT = Path(__file__).resolve().parents[1]
LIBRARIES = ["SqliteVerifier", "EngineeringExamples", "GatePaths", "GateCore"]
"""The libraries that the runtime build names."""


def generator() -> ModuleType:
    """Load the build script, which is not in a package."""
    specification = importlib.util.spec_from_file_location("library_lakefile", ROOT / "build-support/library_lakefile.py")
    assert specification is not None and specification.loader is not None
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


def test_runtime_lakefile_keeps_libraries_and_drops_build_only_parts() -> None:
    """`library_lakefile` keeps the root lakefile's library declarations exactly, keeps the model package,
    drops `lean4export` and the executables, and turns the artifact cache off for read-only outputs."""
    root = tomllib.loads((ROOT / "lakefile.toml").read_text())
    result = tomllib.loads(generator().library_lakefile(root, LIBRARIES))
    declared = {entry["name"]: entry for entry in root["lean_lib"]}
    assert [entry["name"] for entry in result["lean_lib"]] == LIBRARIES
    for entry in result["lean_lib"]:
        assert entry == {key: value for key, value in declared[entry["name"]].items() if key in ("name", "roots", "globs")}
    assert [requirement["name"] for requirement in result["require"]] == ["belaySqlite"]
    assert result["enableArtifactCache"] is False and "lean_exe" not in result
    assert (result["name"], result["version"]) == (root["name"], root["version"])


def test_unknown_library_is_refused() -> None:
    """`library_lakefile` refuses a library that the root lakefile does not declare, naming it."""
    root = tomllib.loads((ROOT / "lakefile.toml").read_text())
    with pytest.raises(SystemExit, match="Absent"):
        generator().library_lakefile(root, ["SqliteVerifier", "Absent"])
