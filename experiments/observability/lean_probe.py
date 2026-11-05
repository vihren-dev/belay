"""Measure Lean and Lake's ordinary CLI output without compiler interception."""

import json
from pathlib import Path
import shutil
import sys

from probe_support import run, write_json


def measure(root: Path, output: Path) -> None:
    """Exercise profiling, diagnostics, dependency exports and module-level reuse."""
    output.mkdir()
    work = output / "work"
    work.mkdir()
    for name in ("Probe.lean", "ProbeModel.lean", "lakefile.toml"):
        shutil.copyfile(Path(__file__).with_name(name), work / name)
    (work / "ProbeUnused.lean").write_text("/-! An unrelated source for invalidation checks. -/\n")
    version = run(output, "lean-version", ["lean", "--version"], cwd=work).stdout.strip()
    lake_version = run(output, "lake-version", ["lake", "--version"], cwd=work).stdout.strip()
    run(output, "fresh", ["lake", "--no-cache", "build", "Probe"], cwd=work)
    artifact = work / ".lake/build/lib/lean/Probe.olean"
    before = artifact.stat().st_mtime_ns
    run(output, "reuse", ["lake", "--no-build", "build", "Probe"], cwd=work)
    assert artifact.stat().st_mtime_ns == before
    with (work / "ProbeUnused.lean").open("a") as stream:
        stream.write("/-- An unrelated value. -/\ndef unused : Nat := 3\n")
    run(output, "unrelated", ["lake", "--no-build", "build", "Probe"], cwd=work)
    assert artifact.stat().st_mtime_ns == before
    with (work / "ProbeModel.lean").open("a") as stream:
        stream.write("/-- A new declaration in an imported module. -/\ndef unusedInImport : Nat := 7\n")
    changed = run(output, "changed-check", ["lake", "--no-build", "build", "Probe"], cwd=work, expected=None)
    assert changed.returncode != 0
    run(output, "changed-build", ["lake", "--no-cache", "build", "Probe"], cwd=work)
    assert artifact.stat().st_mtime_ns != before
    deps = run(output, "imports", ["lake", "env", "lean", "--deps", "Probe.lean"], cwd=work).stdout
    assert "ProbeModel.olean" in deps
    messages = run(output, "messages", ["lake", "env", "lean", "--json", "Probe.lean"], cwd=work)
    parsed = [json.loads(line) for line in messages.stdout.splitlines()]
    assert any("Probe.fromLemma" in json.dumps(item) for item in parsed)
    run(output, "profile-text", ["lake", "env", "lean", "--profile", "Probe.lean"], cwd=work)
    profile = output / "profile.json"
    run(output, "profile-json", ["lake", "env", "lean", "-Dtrace.profiler=true",
        "-Dtrace.profiler.threshold=0", "-Dtrace.profiler.output=" + str(profile), "Probe.lean"], cwd=work)
    profiling = json.loads(profile.read_text())
    assert profiling.get("threads"), profiling.keys()
    invalid = work / "Invalid.lean"
    invalid.write_text('/-! A deliberate type error to check diagnostic extraction. -/\ndef bad : Nat := "wrong"\n')
    failure = run(output, "invalid", ["lake", "env", "lean", "--json", "Invalid.lean"], cwd=work, expected=1)
    errors = [json.loads(line) for line in failure.stdout.splitlines()]
    assert any(item.get("severity") == "error" for item in errors)
    admitted = work / "Admitted.lean"
    admitted.write_text('/-! A deliberately admitted proof for the axiom audit probe. -/\n'
                        '/-- This intentionally unproved claim must expose sorryAx. -/\n'
                        'theorem unproved : False := by sorry\n#print axioms unproved\n')
    axioms = run(output, "admitted", ["lake", "env", "lean", "--json", "Admitted.lean"], cwd=work)
    assert "sorryAx" in axioms.stdout
    manifest = work / "manifest.json"
    write_json(manifest, {"modules": [{"name": name, "source": name + ".lean", "package": "probe"}
                                     for name in ("Probe", "ProbeModel")]})
    run(output, "declarations", [sys.executable, "-m", "tools.theorem_dependencies", "--root", str(root),
        "--lean", str(Path(shutil.which("lean") or "").resolve()), "--output", str(output / "dependencies"),
        "--manifest", str(manifest), "--lean-path", str(work / ".lake/build/lib/lean")],
        cwd=work, environment={"PYTHONPATH": str(root)})
    graph = json.loads((output / "dependencies/dependencies.json").read_text())
    lemma = next(item for item in graph["declarations"] if item["name"] == "Probe.fromLemma")
    assert "ProbeModel.zero" in lemma["bodyReferences"]
    write_json(output / "summary.json", {
        "lean": version, "lake": lake_version, "reuse_preserved_artifact": True,
        "unrelated_source_preserved_artifact": True, "import_change_invalidated": True,
        "changed_check_exit": changed.returncode, "diagnostic_fields": sorted(parsed[0]),
        "profile_bytes": profile.stat().st_size, "profile_threads": len(profiling["threads"]),
        "dependency_modules": graph["coverage"]["loadedModules"],
        "declarations": len(graph["declarations"]), "proof_body_references": lemma["bodyReferences"],
        "admitted_proof_reported_sorryAx": True,
        "runtime_coverage": "No runtime path collector used; profiles measure elaboration, not model paths."})
