"""The proof author's phases: generate, check, audit and export (ADR 0010 section 10).

`generate` writes the generated modules and the audit module into the proofs
project; `check` builds the project with Lake (the per-edit loop); `audit` builds
the audit module, which fails on axioms outside the gate's allowlist and on imports
the verifier does not have; `export` writes the bundle for `verify-bundle`. `prepare`
runs all four and audits before it exports; `export` alone does not audit. Each phase
runs in the agent's trust domain and decides nothing.
"""

import argparse
from collections.abc import Sequence
import json
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from .compile import EXPECTED_SOURCE
from .contract_build import LIBRARY_PREFIXES, selected_cache
from .diagnostics import Rejection
from .elaboration_commands import elaboration_commands
from .import_path import merged_search_path
from .inputs import GeneratedInputs
from .lake_workspace import lake_build
from .project_discovery import Discovery, check_lakefile, discover_project
from .proofs_project import AUDIT_LIBRARY, AUDIT_MODULE, GENERATED_MODULES, link_runtime, write_generated
from .runtime import Runtime
from .source_closure import CompileError, module_path

EXPORT_ROOTS = ("Proofs.migrationCorrect", "Proofs.migrationViolated",
                "NextInterpretation.next", "NextInterpretation.failures")
"""Positive/refutation proofs and interpretation inputs required by the bundle checker."""

PROTECTED_BASE_MODULE = "SqliteVerifier"
"""Protected library that GateCore.baseModules always imports for the verification target."""

TOOLCHAIN_PREFIXES = ("Init", "Std", "Lean")
"""Modules of the pinned Lean installation, which the verifier also has."""


def audit_source(discovery: Discovery) -> str:
    """The audit module: it imports the proofs and allows the toolchain, the library and the project's modules."""
    allowed = [*TOOLCHAIN_PREFIXES, *LIBRARY_PREFIXES, *discovery.contract.order, *GENERATED_MODULES,
               *discovery.candidates]
    theorems = ", ".join(root for root in EXPORT_ROOTS if root.startswith("Proofs."))
    return (f"import Proofs\nimport SqliteVerifier.Audit\n\n"
            f"#belay_audit [{theorems}] allowing [{', '.join(json.dumps(name) for name in allowed)}]\n")


def generate_project(options: argparse.Namespace, inputs: GeneratedInputs) -> tuple[Discovery, dict[str, object]]:
    """Link the runtime, check the sources and the lakefile, and write the generated modules."""
    project = options.project.resolve(strict=True)
    link_runtime(project, inputs.runtime.root)
    with TemporaryDirectory(prefix="generate-") as temporary:
        try:
            discovery = discover_project(runtime=inputs.runtime, requirements=options.requirements,
                                         interpretation=options.interpretation, project=project,
                                         workspace=Path(temporary))
        except CompileError as error:
            raise Rejection("UNVERIFIED", str(error)) from error
    check_lakefile(project, options.requirements, discovery)
    written = write_generated(project, {"SchemaInputs": inputs.schema_source, "SqlInputs": inputs.sql_source,
                                        "Generated": EXPECTED_SOURCE, AUDIT_MODULE: audit_source(discovery)})
    warnings = elaboration_commands({name: source.contents for name, source in discovery.contract.sources.items()})
    return discovery, {"written_modules": written, "warnings": [
        f"{place} runs code while Lean compiles the approved contract, so a cached output can differ from a "
        "fresh one; review that command, or run with --no-cache" for place in warnings]}


def build_project(options: argparse.Namespace, runtime: Runtime, targets: Sequence[str] = ()) -> list[str]:
    """Build the proofs project (default: its default targets) with the selected cache."""
    with selected_cache(options, runtime) as cache:
        try:
            return list(lake_build(options.project.resolve(strict=True), runtime.sysroot, cache, LIBRARY_PREFIXES,
                                   targets))
        except CompileError as error:
            raise Rejection("UNVERIFIED", str(error)) from error


def export_bundle(*, runtime: Runtime, outputs: Path, trusted_imports: frozenset[str], output: Path,
                  timeout: float = 60) -> None:
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


def check(options: argparse.Namespace) -> dict[str, object]:
    """`check`: build the project's default targets, the loop after every proof edit."""
    return {"status": "CHECKED", "compiled_modules": build_project(options, Runtime.locate())}


def audit(options: argparse.Namespace) -> dict[str, object]:
    """`audit`: build the audit module; a failure names the cause."""
    return {"status": "AUDITED", "compiled_modules": build_project(options, Runtime.locate(), (AUDIT_LIBRARY,))}


def export(options: argparse.Namespace, runtime: Runtime, discovery: Discovery) -> dict[str, object]:
    """Write the bundle from the project's built outputs, without the audit.

    The audit is a convenience; `verify-bundle` is the judge. A bundle with `sorry` can
    still be exported and is rejected there, so tools other than `prepare` stay possible.
    """
    if not runtime.exporter.is_file():
        raise Rejection("INPUT_ERROR", f"Proof exporter is missing: {runtime.exporter}; run just build or reinstall")
    export_bundle(runtime=runtime, outputs=options.project.resolve() / ".lake/build/lib/lean",
                  trusted_imports=discovery.trusted_imports, output=options.output.resolve())
    return {"status": "PREPARED", "bundle": str(options.output), "compiled_modules": []}
