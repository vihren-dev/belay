"""`prepare`: build the user's proofs project and export a bundle (ADR 0003 data path, ADR 0010).

The proofs project is a Lake project with the user's own lakefile (`proofs_project`).
`prepare` writes the generated modules into it, checks that its lakefile lists every
module Lake must build, builds it with Lake and the caller's artifact cache, and
exports the proof closure with the pinned lean4export, omitting declarations from the
trusted library. It runs in the agent's trust domain: nothing it builds or caches is
trusted by `verify-bundle`, which compiles the contract itself.
"""

import argparse
import json
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from .compile import EXPECTED_SOURCE
from .contract import Contract, discover_contract
from .contract_build import LIBRARY_PREFIXES, selected_cache
from .diagnostics import Rejection
from .import_path import merged_search_path
from .inputs import generated_inputs
from .lake_workspace import lake_build
from .proofs_project import GENERATED_MODULES, link_runtime, missing_modules, reads_contract_from, write_generated
from .runtime import Runtime
from .source_closure import CompileError, Source, discover_sources, module_path, role_sources

EXPORT_ROOTS = ("Proofs.migrationCorrect", "Proofs.migrationViolated",
                "NextInterpretation.next", "NextInterpretation.failures")
"""Positive/refutation proofs and interpretation inputs required by the bundle checker."""

PROTECTED_BASE_MODULE = "SqliteVerifier"
"""Protected library that GateCore.baseModules always imports for the verification target."""

CANDIDATE_ROOTS = ("NextInterpretation", "Proofs")
"""Candidate modules that every proofs project has, at its top level."""


def discover_project(*, runtime: Runtime, requirements: Path, interpretation: Path, project: Path,
                     workspace: Path) -> tuple[Contract, tuple[str, ...], set[str]]:
    """The approved closure, the candidate modules and the trusted imports, under today's source rules.

    Candidate modules may import the contract and the generated inputs but not provide
    their own `SchemaInputs` or `SqlInputs`.
    """
    selected = {"Requirements": requirements.resolve(strict=True), "Interpretation": interpretation.resolve(strict=True)}
    contract = discover_contract(
        initial=role_sources(selected), roots=tuple(dict.fromkeys(path.parent for path in selected.values())),
        excluded=set(), directory=workspace / "approved", sysroot=runtime.sysroot, libraries=runtime.libraries,
        workspace=workspace)
    external: set[str] = set(contract.external)
    initial = {name: Source(path, path.read_bytes()) for name in CANDIDATE_ROOTS
               for path in [(project / f"{name}.lean").resolve(strict=True)]}
    initial["Generated"] = Source(None, EXPECTED_SOURCE.encode())
    _, order = discover_sources(
        initial=initial, roots=(project,), excluded=set(), forbidden={"SchemaInputs", "SqlInputs"},
        available=set(contract.sources) | {"SchemaInputs", "SqlInputs"}, directory=workspace / "candidate",
        sysroot=runtime.sysroot, libraries=runtime.libraries, workspace=workspace, external=external)
    return contract, tuple(name for name in order if name != "Generated"), external


def export_bundle(*, runtime: Runtime, outputs: Path, trusted_imports: set[str], output: Path,
                  timeout: float) -> None:
    """Use the header's trusted imports and protected base to omit exactly the checker library closure."""
    roots = (runtime.sysroot / "lib/lean", *runtime.libraries, outputs)
    requested = [module_path(name) for name in trusted_imports | {PROTECTED_BASE_MODULE}]
    requested.extend(path.relative_to(outputs).with_suffix("") for path in outputs.rglob("*.olean"))
    with TemporaryDirectory(prefix="export-") as scratch, \
            merged_search_path(roots, Path(scratch), requested=requested) as paths, \
            output.open("w", encoding="utf-8") as stream:
        environment = {"LEAN_SYSROOT": str(runtime.sysroot), "PATH": os.environ.get("PATH", ""),
                       "LEAN_PATH": os.pathsep.join(map(str, paths))}
        stream.write(json.dumps({"bundle": 1, "trusted_imports": sorted(trusted_imports)}) + "\n")
        stream.flush()
        omitted = sorted(trusted_imports | {PROTECTED_BASE_MODULE})
        result = subprocess.run([str(runtime.exporter), *["--omit=" + module for module in omitted],
                                 "--ignore-missing", "Proofs", "--", *EXPORT_ROOTS], env=environment, stdout=stream,
                                stderr=subprocess.PIPE, text=True, timeout=timeout, check=False)
    if result.returncode:
        raise Rejection("UNVERIFIED", f"Proof exporter {runtime.exporter} failed: {result.stderr.strip()}; "
                        "check the candidate imports and proof declarations")


def prepare(options: argparse.Namespace) -> dict[str, object]:
    """Build the proofs project against the approved contract and export a bundle to `--output`."""
    inputs = generated_inputs(options)
    runtime = inputs.runtime
    if not runtime.exporter.is_file():
        raise Rejection("INPUT_ERROR", f"Proof exporter is missing: {runtime.exporter}; run just build or reinstall")
    project = options.project.resolve(strict=True)
    link_runtime(project, runtime.root)
    write_generated(project, {"SchemaInputs": inputs.schema_source, "SqlInputs": inputs.sql_source,
                              "Generated": EXPECTED_SOURCE})
    with TemporaryDirectory(prefix="prepare-") as temporary:
        try:
            contract, candidates, trusted_imports = discover_project(
                runtime=runtime, requirements=options.requirements, interpretation=options.interpretation,
                project=project, workspace=Path(temporary))
        except CompileError as error:
            raise Rejection("UNVERIFIED", str(error)) from error
    lakefile = project / "lakefile.toml"
    if lakefile.is_file():
        text = lakefile.read_text(encoding="utf-8")
        approved = options.requirements.resolve().parent
        if not reads_contract_from(text, project, approved):
            raise Rejection("INPUT_ERROR", f"{lakefile} has no library that reads Requirements and Interpretation "
                            f"from {approved}; set that library's srcDir to the approved folder")
        missing = missing_modules(text, [*contract.order, *GENERATED_MODULES, *candidates])
        if missing:
            raise Rejection("INPUT_ERROR", f"{lakefile} lists no library for the modules {', '.join(missing)}; "
                            "add each one to the roots of the library whose folder holds it")
    with selected_cache(options, runtime) as cache:
        try:
            compiled = lake_build(project, runtime.sysroot, cache, LIBRARY_PREFIXES)
        except CompileError as error:
            raise Rejection("UNVERIFIED", str(error)) from error
    export_bundle(runtime=runtime, outputs=project / ".lake/build/lib/lean", trusted_imports=trusted_imports,
                  output=options.output.resolve(), timeout=60)
    return {"status": "PREPARED", "bundle": str(options.output), "compiled_modules": list(compiled)}
