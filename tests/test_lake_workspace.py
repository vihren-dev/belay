"""`migration_check.lake_workspace`: the generated lakefile and the reading of Lake's output."""

from pathlib import Path
import subprocess
import tomllib

import pytest

from migration_check import lake_workspace
from migration_check.lake_workspace import Library, compiled_modules, failed_targets, lakefile

pytestmark = pytest.mark.unit

FAILED_OUTPUT = """\
✔ [26/34] Built SchemaInputs (197ms)
✖ [27/34] Building Requirements (84ms)
error: Requirements.lean:3:0: unknown identifier 'x'
Some required targets logged failures:
- Requirements
- Interpretation
error: build failed
"""
"""Lake's output when two contract modules fail, as Lake 5.0.0 prints it without ANSI codes."""


def test_lakefile_requires_runtime_and_declares_libraries() -> None:
    """`lakefile` writes TOML with the cache on, outputs restored to the workspace, the runtime required by
    path, and one library per entry; the verifier reads this file back with a TOML parser only."""
    text = lakefile("verification", Path("/runtime"), [Library("Contract", "approved", ("Requirements",)),
                                                       Library("GeneratedInputs", "generated", ("SchemaInputs",))])
    parsed = tomllib.loads(text)
    assert parsed["enableArtifactCache"] is True and parsed["restoreAllArtifacts"] is True
    assert parsed["defaultTargets"] == ["Contract", "GeneratedInputs"]
    assert parsed["require"] == [{"name": "sqliteVerifier", "path": "/runtime"}]
    assert parsed["lean_lib"][1] == {"name": "GeneratedInputs", "srcDir": "generated", "roots": ["SchemaInputs"]}


def test_failed_targets_and_compiled_modules_from_output() -> None:
    """`failed_targets` reads Lake's failure list, and `compiled_modules` the compiled modules without the
    installed library's, so diagnostics name the failing module and tests can count compiles."""
    assert failed_targets(FAILED_OUTPUT) == ("Requirements", "Interpretation")
    assert failed_targets("Build completed successfully.") == ()
    assert compiled_modules("✔ [1/3] Built SqliteVerifier.X\n✔ [2/3] Built Proofs (5ms)\n", ["SqliteVerifier"]) == (
        "Proofs",)


@pytest.mark.parametrize("processors,jobs", [(32, 8), (4, 4), (1, 1), (None, 1)])
def test_lake_threads_are_bounded(processors: int | None, jobs: int, monkeypatch: pytest.MonkeyPatch,
                                  tmp_path: Path) -> None:
    """`lake_build` gives Lake `LEAN_NUM_THREADS` = the processor count, at most `MAX_PARALLEL_JOBS`, because
    Lake has no jobs option and its thread pool sets its parallel builds."""
    seen: dict[str, str] = {}

    def runner(_arguments: object, *, write_root: Path, environment: dict[str, str],
               timeout: float) -> subprocess.CompletedProcess[str]:
        """Record the environment instead of starting Lake."""
        seen.update(environment)
        return subprocess.CompletedProcess([], 0, "", "")
    monkeypatch.setattr(lake_workspace.os, "cpu_count", lambda: processors)
    monkeypatch.setattr(lake_workspace, "run_process", runner)
    assert lake_workspace.lake_build(tmp_path, tmp_path, tmp_path / "cache", ["SqliteVerifier"]) == ()
    assert seen == {"LAKE_CACHE_DIR": str(tmp_path / "cache"), "LEAN_NUM_THREADS": str(jobs)}
