"""The installed runtime is a Lake package that Lake replays without compiling (ADR 0010 section 3).

Proofs projects and the verifier's own workspaces require the runtime by path.
If Lake compiled a library module, the runtime's outputs or traces would be
incomplete (for example missing `ir`), and every build would rebuild the library
or fail on the read-only installation.
"""

from collections.abc import Callable
import os
from pathlib import Path
import re
import subprocess

import pytest

from migration_check.lake_workspace import Library, lake_build, write_workspace
from migration_check.source_closure import CompileError
from tests.runtime_support import CommandResult

pytestmark = [pytest.mark.integration, pytest.mark.requires_lean]

LIBRARY_PREFIXES = ("SqliteVerifier", "Belay", "GateCore", "GatePaths")
"""Module prefixes that the runtime package and its model package provide."""


def test_workspace_requiring_runtime_compiles_no_library_module(
        runtime_root: Path, tmp_path: Path, command_runner: Callable[..., CommandResult]) -> None:
    """A workspace that imports the library and an engineering example builds; Lake compiles only its own module."""
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    (workspace / "lean-toolchain").write_text((runtime_root / "lean-toolchain").read_text())
    (workspace / "lakefile.toml").write_text(
        'name = "probe"\ndefaultTargets = ["Probe"]\nenableArtifactCache = true\n\n'
        f'[[require]]\nname = "sqliteVerifier"\npath = "{runtime_root}"\n\n'
        '[[lean_lib]]\nname = "Probe"\nroots = ["Probe"]\n')
    (workspace / "Probe.lean").write_text(
        "import SqliteVerifier\nimport SqliteVerifier.Demonstration\nimport Belay.Sqlite\n"
        "example : True := trivial\n")
    environment = {"HOME": str(tmp_path), "PATH": f"{runtime_root / 'lean/bin'}{os.pathsep}/usr/bin:/bin",
                   "LAKE_CACHE_DIR": str(tmp_path / "cache")}
    result = command_runner(["lake", "build"], cwd=workspace, timeout=120, environment=environment)
    assert result.returncode == 0, result.diagnostic()
    built = [line for line in result.stdout.splitlines() if "Built " in line]
    assert [line for line in built if any(f"Built {prefix}" in line for prefix in LIBRARY_PREFIXES)] == [], built
    assert any("Built Probe" in line for line in built), result.diagnostic()


def test_lake_build_reuses_cache_and_names_failed_module(runtime_root: Path, tmp_path: Path) -> None:
    """`lake_build` runs through the bounded process runner: a new directory with the same cache compiles
    nothing, and a module that fails is named in the `CompileError`."""
    def workspace(name: str, body: str) -> Path:
        """A one-module workspace in its own directory."""
        directory = tmp_path / name
        write_workspace(directory, "probe", runtime_root, [Library("Probe", ".", ("Probe",))])
        (directory / "Probe.lean").write_text("import SqliteVerifier\n" + body)
        return directory

    cache, sysroot, prefixes = tmp_path / "cache", runtime_root / "lean", LIBRARY_PREFIXES
    assert lake_build(workspace("first", "def x : Nat := 1\n"), sysroot, cache, prefixes) == ("Probe",)
    assert lake_build(workspace("second", "def x : Nat := 1\n"), sysroot, cache, prefixes) == ()
    with pytest.raises(CompileError) as failure:
        lake_build(workspace("broken", "def x : Nat := true\n"), sysroot, cache, prefixes)
    assert failure.value.module == "Probe" and "Probe.lean" in failure.value.diagnostics


def test_lake_build_over_its_deadline_is_stopped(runtime_root: Path, tmp_path: Path) -> None:
    """`lake_build` passes its deadline to the bounded runner, which stops Lake and reports the timeout."""
    write_workspace(tmp_path / "slow", "probe", runtime_root, [Library("Probe", ".", ("Probe",))])
    (tmp_path / "slow/Probe.lean").write_text("import SqliteVerifier\ndef x : Nat := 1\n")
    with pytest.raises(subprocess.TimeoutExpired):
        lake_build(tmp_path / "slow", runtime_root / "lean", tmp_path / "cache", LIBRARY_PREFIXES, timeout=0.05)


def test_toolchain_reports_its_commit(runtime_root: Path, tmp_path: Path,
                                      command_runner: Callable[..., CommandResult]) -> None:
    """The pinned `lean --version` names the toolchain's commit: Lake puts it in every cache key, and a Lean
    that reports only a release tag gets keys that never match a cache (ledger/ledger#3270)."""
    result = command_runner([str(runtime_root / "lean/bin/lean"), "--version"], cwd=tmp_path, timeout=30)
    assert result.returncode == 0 and re.search(r"commit [0-9a-f]{40}", result.stdout), result.diagnostic()
