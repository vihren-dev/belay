"""Check the compiled dependency exporter against proofs with distinct reference paths."""

import json
import os
from pathlib import Path
import shutil
import subprocess
from typing import cast

import pytest

from tools.theorem_dependencies import export_dependencies

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests/theorem_dependencies"
pytestmark = [pytest.mark.integration, pytest.mark.environment]


def export(runtime: Path, directory: Path, modules: list[dict[str, str]],
           output: str = "dependencies.json") -> subprocess.CompletedProcess[str]:
    """Run the shipped exporter with explicit compiled-module scope and a bounded wait."""
    manifest = directory / "manifest.json"
    manifest.write_text(json.dumps({"modules": modules}))
    return subprocess.run(
        [str(runtime / "lean/bin/lean"), "--run",
         str(ROOT / "tools/theorem_dependency_exporter.lean"),
         str(manifest), str(directory / output)],
        cwd=directory, env={**os.environ, "LEAN_PATH": str(directory), "LEAN_SYSROOT": str((runtime / "lean").resolve())},
        capture_output=True, text=True, timeout=30,
    )


@pytest.fixture(scope="module")
def compiled_report(tmp_path_factory: pytest.TempPathFactory, runtime_root: Path
                    ) -> tuple[Path, list[dict[str, str]], dict[str, object]]:
    """Compile original fixtures, including a module outside the main import closure."""
    directory = tmp_path_factory.mktemp("theorem-dependencies")
    modules: list[dict[str, str]] = []
    for name in ("DependencyFixture", "Standalone"):
        source = directory / f"{name}.lean"
        shutil.copyfile(FIXTURES / source.name, source)
        result = subprocess.run(
            [str(runtime_root / "lean/bin/lean"), "-o", f"{name}.olean", "-i", f"{name}.ilean", source.name],
            cwd=directory, env={**os.environ, "LEAN_PATH": str(directory), "LEAN_SYSROOT": str((runtime_root / "lean").resolve())},
            capture_output=True, text=True, timeout=30,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        modules.append({"name": name, "source": str(source), "package": "fixture"})
    result = export(runtime_root, directory, modules)
    assert result.returncode == 0, result.stdout + result.stderr
    return directory, modules, cast(dict[str, object], json.loads((directory / "dependencies.json").read_text()))


def objects(report: dict[str, object], field: str) -> list[dict[str, object]]:
    """Read rows from the exporter contract for assertions about observable output."""
    return cast(list[dict[str, object]], report[field])


def references(declaration: dict[str, object], field: str = "bodyReferences") -> list[str]:
    """Keep statement and proof references separate in fixture assertions."""
    return cast(list[str], declaration[field])


def test_compiled_proof_dependencies_include_tactic_private_and_generated_paths(
    compiled_report: tuple[Path, list[dict[str, str]], dict[str, object]],
) -> None:
    """The exporter retains elaborated proof edges that a source-only or theorem-only graph loses."""
    _, _, report = compiled_report
    declarations = {str(row["name"]): row for row in objects(report, "declarations")}
    statement = declarations["DependencyFixture.statementOnly"]
    assert "DependencyFixture.statementPredicate" in references(statement, "typeReferences")
    assert "DependencyFixture.statementPredicate" not in references(statement)
    assert statement["bodyAvailable"] is True
    assert "DependencyFixture.unwrap._simp_1" in references(declarations["DependencyFixture.tacticSelected"])
    assert "DependencyFixture.unwrap" in references(declarations["DependencyFixture.unwrap._simp_1"])
    assert declarations["DependencyFixture.Wrapped.intro"]["bodyAvailable"] is False
    assert references(declarations["DependencyFixture.Wrapped.intro"]) == []
    private = [name for name, row in declarations.items() if row["displayName"] == "DependencyFixture.privateProof"]
    assert len(private) == 1 and private[0].startswith("_private.DependencyFixture.")
    assert declarations[private[0]]["private"] is True
    entry = "DependencyFixture.throughGenerated"
    frontier = [(entry, [entry])]
    visited: set[str] = set()
    paths: list[list[str]] = []
    while frontier:
        name, path = frontier.pop()
        if name == private[0]:
            paths.append(path)
        if name in visited or name not in declarations:
            continue
        visited.add(name)
        frontier.extend((target, [*path, target]) for target in references(declarations[name]))
    assert paths and all(len(path) > 2 for path in paths)
    assert any(declarations[name]["kind"] == "definition" for path in paths for name in path[1:-1])
    assert any(declarations[name]["internal"] for path in paths for name in path[1:-1])
    assert any(row["name"] == "True.intro" for row in objects(report, "external"))


def test_selected_scope_source_ranges_and_repeatability(
    compiled_report: tuple[Path, list[dict[str, str]], dict[str, object]], runtime_root: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The exporter includes separate selections, preserves UTF-16 ranges and sorts output deterministically."""
    directory, modules, report = compiled_report
    assert report["schemaVersion"] == 1 and report["leanVersion"]
    assert {row["name"] for row in objects(report, "modules")} == {"DependencyFixture", "Standalone"}
    declarations = objects(report, "declarations")
    assert {row["module"] for row in declarations} == {"DependencyFixture", "Standalone"}
    assert any(row["name"] == "Standalone.selectedSeparately" for row in declarations)
    statement = next(row for row in declarations if row["name"] == "DependencyFixture.statementOnly")
    source_lines = (directory / "DependencyFixture.lean").read_text().splitlines()
    line = next(index for index, text in enumerate(source_lines) if text.startswith("theorem statementOnly"))
    assert statement["selection"] == [line, 8, line, 21]
    unicode = next(row for row in declarations if row["name"] == "DependencyFixture.unicodeSelected")
    line = next(index for index, text in enumerate(source_lines) if text.startswith("/- 𝄞 -/ theorem"))
    prefix, _, _ = source_lines[line].partition("unicodeSelected")
    column = len(prefix.encode("utf-16-le")) // 2
    assert unicode["selection"] == [line, column, line, column + len("unicodeSelected")]
    assert all(row["imports"] and str(row["sourceHash"]).isdigit() for row in objects(report, "modules"))
    poisoned = directory / "poisoned-bin"
    poisoned.mkdir()
    (poisoned / "lean").write_text("#!/bin/sh\nexit 123\n")
    (poisoned / "lean").chmod(0o755)
    monkeypatch.setenv("PATH", str(poisoned))
    result = export(runtime_root, directory, list(reversed(modules)), "repeat.json")
    assert result.returncode == 0, result.stdout + result.stderr
    assert (directory / "dependencies.json").read_bytes() == (directory / "repeat.json").read_bytes()


def test_source_hash_normalizes_line_endings(
    compiled_report: tuple[Path, list[dict[str, str]], dict[str, object]], runtime_root: Path,
) -> None:
    """The exporter's source hash matches proof-cost normalization for Windows line endings."""
    directory, modules, _ = compiled_report
    source = Path(modules[0]["source"])
    original = source.read_bytes()
    try:
        source.write_bytes(original.replace(b"\n", b"\r\n"))
        result = export(runtime_root, directory, modules, "crlf.json")
        assert result.returncode == 0, result.stdout + result.stderr
        assert (directory / "dependencies.json").read_bytes() == (directory / "crlf.json").read_bytes()
    finally:
        source.write_bytes(original)


def test_missing_private_artifact_fails(
    compiled_report: tuple[Path, list[dict[str, str]], dict[str, object]], runtime_root: Path, tmp_path: Path,
) -> None:
    """The exporter requires split private data instead of silently losing compiled theorem bodies."""
    directory, modules, _ = compiled_report
    assert (directory / "Standalone.olean.private").exists()
    for artifact in directory.glob("Standalone.*"):
        if artifact.name != "Standalone.olean.private":
            shutil.copyfile(artifact, tmp_path / artifact.name)
    result = export(runtime_root, tmp_path, [modules[1]])
    assert result.returncode != 0
    assert "Standalone.olean.private" in result.stdout + result.stderr
    assert not (tmp_path / "dependencies.json").exists()


@pytest.mark.parametrize("damage", ["missing-module", "missing-source", "duplicate", "empty"])
def test_invalid_selected_scope_fails(
    compiled_report: tuple[Path, list[dict[str, str]], dict[str, object]], runtime_root: Path,
    tmp_path: Path, damage: str,
) -> None:
    """The exporter fails explicit selections that would otherwise produce misleading coverage."""
    _, original, _ = compiled_report
    modules = [dict(module) for module in original]
    if damage == "missing-module":
        modules[0]["name"] = "MissingFixture"
        expected = "MissingFixture"
    elif damage == "missing-source":
        modules[0]["source"] = str(tmp_path / "missing.lean")
        expected = "Source for module DependencyFixture is missing"
    elif damage == "duplicate":
        modules.append(dict(modules[0]))
        expected = "selected twice"
    else:
        modules = []
        expected = "is empty"
    result = export(runtime_root, tmp_path, modules)
    assert result.returncode != 0
    assert expected in result.stdout + result.stderr
    assert not (tmp_path / "dependencies.json").exists()


def test_report_pipeline_preserves_compiled_provenance(
    compiled_report: tuple[Path, list[dict[str, str]], dict[str, object]], runtime_root: Path, tmp_path: Path,
) -> None:
    """The shipped pipeline exports real proofs, embeds sources and identifies every selected artifact."""
    directory, modules, _ = compiled_report
    manifest = tmp_path / "selected.json"
    manifest.write_text(json.dumps({"modules": modules}))
    report = export_dependencies(directory, runtime_root / "lean/bin/lean",
        tmp_path / "report", manifest=manifest, lean_path=[directory])
    assert (tmp_path / "report/index.html").is_file()
    assert cast(dict[str, object], report["coverage"])["loadedModules"] == len(modules)
    assert all(row["sourceText"] and row["artifactFiles"] for row in objects(report, "modules"))
