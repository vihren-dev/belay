"""Check dependency scope, source identity, shared-root imports and optional cost matching."""

import json
from pathlib import Path

import pytest

from tools.theorem_dependency_costs import attach_costs
from tools.theorem_dependency_manifest import (
    PACKAGES, Module, default_modules, merge_libraries, read_manifest, selected_artifacts,
)

def test_default_scope_includes_sources_outside_umbrella_imports(tmp_path: Path) -> None:
    """Default scope finds a library's separately built source without parsing umbrella imports."""
    for package, tree in PACKAGES.items():
        folder = tmp_path / "packages" / package
        (folder / tree).mkdir(parents=True)
        (folder / tree / f"{package.replace('-', '_')}.lean").write_text("def separate := 1\n")
        (folder / "lakefile.lean").write_text("import Lake\n")
    (tmp_path / "packages/belay/Belay.lean").write_text("-- No imports\n")
    (tmp_path / "packages/belay/BelaySqlCheck.lean").write_text("import Lake\n")
    modules = default_modules(tmp_path)
    assert len(modules) == 5
    assert {module["package"] for module in modules} == set(PACKAGES)
    assert not any("lakefile" in module["name"] or "BelaySqlCheck" in module["name"] for module in modules)


def test_manifest_paths_are_relative_to_the_manifest(tmp_path: Path) -> None:
    """Explicit manifests select orphan fixture modules independently of the process directory."""
    path = tmp_path / "manifest.json"
    path.write_text(json.dumps({"modules": [{"name": "Separate", "source": "Separate.lean", "package": "fixture"}]}))
    assert read_manifest(path) == [Module(name="Separate", source=str(tmp_path / "Separate.lean"), package="fixture")]
    path.write_text(json.dumps({"modules": read_manifest(path) * 2}))
    with pytest.raises(ValueError, match="each module name once"):
        read_manifest(path)


def test_missing_artifact_fails_complete_selection(tmp_path: Path) -> None:
    """The report cannot claim completeness when a separately selected source was not compiled."""
    source = tmp_path / "Separate.lean"
    source.write_text("def separate := 1\n")
    module = Module(name="Separate", source=str(source), package="fixture")
    with pytest.raises(ValueError, match="Separate: missing compiled artifact"):
        selected_artifacts([module], tmp_path)
    artifact = tmp_path / "Separate.olean"
    artifact.write_bytes(b"fixture compiled bytes")
    private = tmp_path / "Separate.olean.private"
    private.write_bytes(b"fixture proof body bytes")
    identities = selected_artifacts([module], tmp_path)["Separate"]
    assert identities["artifact"] == str(artifact)
    assert len(identities["artifactSha256"]) == len(identities["sourceSha256"]) == 64
    assert {row["path"] for row in identities["artifactFiles"]} == {str(artifact), str(private)}


def test_shared_namespace_roots_merge_without_shadowing(tmp_path: Path) -> None:
    """A model and surface module remain discoverable under one shared Belay root."""
    roots = [tmp_path / "model", tmp_path / "surface"]
    for root, module in zip(roots, ("Model", "Run"), strict=True):
        folder = root / "Belay/Sqlite"
        folder.mkdir(parents=True)
        for suffix in ("olean", "olean.private", "olean.server", "ilean", "ir"):
            (folder / f"{module}.{suffix}").write_text(module)
    merged = tmp_path / "merged"
    merge_libraries(roots, merged)
    assert len(list((merged / "Belay/Sqlite").iterdir())) == 10
    assert (merged / "Belay/Sqlite/Run.olean").resolve() == roots[1] / "Belay/Sqlite/Run.olean"


def test_conflicting_compiled_versions_fail_before_extraction(tmp_path: Path) -> None:
    """Ambiguous compiled versions cannot silently select a graph from the wrong build."""
    roots = [tmp_path / "first", tmp_path / "second"]
    for index, root in enumerate(roots):
        root.mkdir()
        (root / "Fixture.olean").write_text(str(index))
    with pytest.raises(ValueError, match="select one compiled version"):
        merge_libraries(roots, tmp_path / "merged")


def cost_graph() -> dict[str, object]:
    """Provide the exporter fields that establish a supplied cost record's identity."""
    return {"leanVersion": "4.34.1", "modules": [{"name": "Fixture", "sourceHash": "123"}],
            "declarations": [{"name": "Fixture.proof", "module": "Fixture"}]}


def cost_record() -> dict[str, object]:
    """Represent the stored S7 JSON format without collecting new measurements."""
    return {"module": "Fixture", "declaration": "Fixture.proof", "compiler": "4.34.1",
            "sourceHash": "123", "status": "completed", "heartbeats": 321,
            "unit": "internal-heartbeat", "scheme": "proof-body-async"}


def test_existing_compatible_costs_attach_by_exact_identity(tmp_path: Path) -> None:
    """The dependency report reuses an existing S7 measurement and leaves absent costs explicit."""
    data = cost_graph()
    attach_costs(data, None)
    assert data["proofCosts"] == []
    path = tmp_path / "costs.json"
    path.write_text(json.dumps({"libraries": [{"records": [cost_record()], "stale": []}]}))
    attach_costs(data, path)
    assert data["proofCosts"] == [{**cost_record(), "name": "Fixture.proof"}]
    assert data["proofCostCoverage"] == {"supplied": True, "attached": 1, "rejected": []}


@pytest.mark.parametrize("field,value", [("compiler", "other"), ("sourceHash", "different"),
    ("status", "failed"), ("heartbeats", None), ("heartbeats", True), ("heartbeats", -1), ("unit", "seconds"),
    ("declaration", "Other.proof")])
def test_incompatible_costs_remain_explicitly_unattached(tmp_path: Path, field: str, value: object) -> None:
    """Costs from another source, compiler, scope or measurement state do not become graph metrics."""
    data, record = cost_graph(), cost_record()
    record[field] = value
    path = tmp_path / "costs.json"
    path.write_text(json.dumps({"libraries": [{"records": [record], "stale": []}]}))
    attach_costs(data, path)
    assert data["proofCosts"] == []
    coverage = data["proofCostCoverage"]
    assert isinstance(coverage, dict) and len(coverage["rejected"]) == 1


def test_numeric_source_hash_matches_and_stale_module_rejects(tmp_path: Path) -> None:
    """S7 small UInt64 hashes use JSON numbers, and a stale-module marker prevents attachment."""
    data, record = cost_graph(), cost_record()
    record["sourceHash"] = 123
    path = tmp_path / "costs.json"
    library: dict[str, object] = {"records": [record], "stale": []}
    path.write_text(json.dumps({"libraries": [library]}))
    attach_costs(data, path)
    assert len(data["proofCosts"]) == 1
    library["stale"] = ["Fixture"]
    path.write_text(json.dumps({"libraries": [library]}))
    attach_costs(data, path)
    assert data["proofCosts"] == []
