"""`prepare`, `generate` and `export`: the proof author's commands that need the SQL inputs (ADR 0010).

`prepare` runs the phases of `project_phases` in order: generate, check, audit and
export. It runs in the agent's trust domain: nothing it builds or caches is trusted
by `verify-bundle`, which compiles the contract itself. `generate` alone refreshes
the generated modules after a SQL change; `export` writes the bundle without the audit.
"""

import argparse

from .diagnostics import Rejection
from .inputs import generated_inputs
from .project_phases import AUDIT_LIBRARY, build_project, export, generate_project


def prepare(options: argparse.Namespace) -> dict[str, object]:
    """Generate, build, audit and export the proofs project; the bundle goes to `--output`."""
    inputs = generated_inputs(options)
    runtime = inputs.runtime
    if not runtime.exporter.is_file():
        raise Rejection("INPUT_ERROR", f"Proof exporter is missing: {runtime.exporter}; run just build or reinstall")
    discovery, generated = generate_project(options, inputs)
    compiled = build_project(options, runtime)
    audited = build_project(options, runtime, (AUDIT_LIBRARY,))
    exported = export(options, runtime, discovery)
    return {**exported, "compiled_modules": [*compiled, *audited], "warnings": generated["warnings"]}


def generate(options: argparse.Namespace) -> dict[str, object]:
    """`generate`: write the generated modules and the audit module into the proofs project."""
    _, generated = generate_project(options, generated_inputs(options))
    return {"status": "GENERATED", **generated}


def export_bundle_command(options: argparse.Namespace) -> dict[str, object]:
    """`export`: write the bundle from the built project, without the audit; it regenerates first, so the
    bundle matches the SQL it names."""
    inputs = generated_inputs(options)
    discovery, generated = generate_project(options, inputs)
    return {**export(options, inputs.runtime, discovery), "warnings": generated["warnings"]}
