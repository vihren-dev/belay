"""Export compiled Lean dependencies and write an offline report for the selected build."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

from tools.theorem_dependency_costs import attach_costs
from tools.theorem_dependency_manifest import (
    EXCLUSIONS, PACKAGES, default_modules, digest, merge_libraries, object_list,
    object_value, read_manifest, selected_artifacts,
)
from tools.theorem_dependency_report import write_report

COMPILER_TIMEOUT_SECONDS = 300
"""Bound each compiler invocation while allowing complete project imports."""


def export_dependencies(root: Path, lean: Path, tools: Path, output: Path,
                        *, manifest: Path | None = None, lean_path: list[Path] | None = None,
                        proof_costs: Path | None = None) -> dict[str, object]:
    """Inspect existing compiled modules, failing incomplete selections before publishing a report."""
    modules = read_manifest(manifest) if manifest else default_modules(root)
    paths = lean_path if lean_path is not None else [
        root / "packages" / package / ".lake/build/lib/lean" for package in PACKAGES]
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="theorem-dependencies-") as temporary:
        work = Path(temporary)
        library = work / "lib"
        merge_libraries(paths, library)
        artifacts = selected_artifacts(modules, library)
        selected = work / "manifest.json"
        selected.write_text(json.dumps({"modules": modules}, indent=2) + "\n")
        environment = dict(os.environ)
        prefix = subprocess.run([str(lean), "--print-prefix"], check=True, text=True,
                                capture_output=True, timeout=COMPILER_TIMEOUT_SECONDS)
        environment["LEAN_SYSROOT"] = prefix.stdout.strip()
        environment["LEAN_PATH"] = str(library)
        exported = work / "dependencies.json"
        subprocess.run([str(lean), "--run", str(tools / "TheoremDependencies.lean"),
                        str(selected), str(exported)], cwd=work, env=environment,
                       check=True, timeout=COMPILER_TIMEOUT_SECONDS)
        data = object_value(json.loads(exported.read_text()), "compiler dependency report")
        loaded = object_list(data.get("modules"), "compiler modules")
        names = [row.get("name") for row in loaded]
        if set(names) != {module["name"] for module in modules} or len(names) != len(modules):
            raise ValueError("Compiler module coverage differs from the manifest; inspect the exporter output")
        for module in loaded:
            name = str(module["name"])
            source = Path(str(module["source"]))
            module.update(artifacts[name])
            module["sourceText"] = source.read_text()
        data["coverage"] = {"selectedModules": len(modules), "loadedModules": len(loaded),
                            "complete": True, "scope": "manifest" if manifest else "default libraries",
                            "exclusions": EXCLUSIONS}
        data["provenance"] = {"compiler": str(lean.resolve()), "manifestSha256": digest(selected),
            "leanPath": [str(path.resolve()) for path in paths],
            "sources": "Sources and artifacts are identified separately; use the Nix target for a matched build."}
        attach_costs(data, proof_costs)
        write_report(data, output / "index.html")
        (output / "dependencies.json").write_text(json.dumps(data, separators=(",", ":")) + "\n")
        (output / "manifest.json").write_text(selected.read_text())
    return data


def main() -> int:
    """Use explicit compiler and library paths so the report does not select an ambient toolchain."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--tools", type=Path, required=True, help="Built packages/public-doc-tools package")
    parser.add_argument("--output", type=Path, required=True, help="Directory for index.html and dependencies.json")
    parser.add_argument("--manifest", type=Path, help="Explicit selected modules; source paths are relative to this file")
    parser.add_argument("--lean-path", help="Compiled library roots separated by the platform path separator; defaults to LEAN_PATH when set")
    parser.add_argument("--proof-costs", type=Path, help="JSON from lake exe belay-sql-check --costs --json")
    arguments = parser.parse_args()
    selected_path = arguments.lean_path if arguments.lean_path is not None else os.environ.get("LEAN_PATH")
    paths = [Path(part).resolve() for part in selected_path.split(os.pathsep) if part] if selected_path else None
    try:
        report = export_dependencies(arguments.root.resolve(), arguments.lean.resolve(),
            arguments.tools.resolve(), arguments.output.resolve(), manifest=arguments.manifest,
            lean_path=paths, proof_costs=arguments.proof_costs)
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        parser.exit(1, f"Dependency report failed: {error}\n")
    print(json.dumps({"report": str(arguments.output / "index.html"), "coverage": report["coverage"]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
