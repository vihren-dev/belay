"""`verify-bundle`: check an exported proof bundle without compiling candidate source (ADR 0003).

The verifier still parses the actual SQL itself. It builds the starting schema and
the approved contract with Lake, reusing outputs from its own artifact cache (ADR
0010), and passes the frontend's structural record to the
checker, which constructs the generated SQL declarations without a Lean compile (ADR
0003 P3). Only the candidate's declarations arrive as data. Statuses and exit codes
match `verify`.
"""

import argparse
import hashlib
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from .contract_build import build_contract, selected_cache
from .diagnostics import Rejection
from .inputs import generated_inputs
from .process import run_process
from .source_closure import CompileError


def verify_bundle(options: argparse.Namespace) -> dict[str, object]:
    """Compile the trusted side, then run the bundle checker on a private copy of the bundle."""
    inputs = generated_inputs(options)
    runtime = inputs.runtime
    if not runtime.bundle_checker.is_file():
        raise Rejection("INPUT_ERROR", "This runtime has no bundle checker; rebuild with ADR 0003 support")
    bundle_bytes = options.bundle.read_bytes()
    with TemporaryDirectory(prefix="migration-bundle-") as temporary, selected_cache(options, runtime) as cache:
        workspace = Path(temporary).resolve()
        try:
            contract, compiled = build_contract(
                runtime=runtime, requirements=options.requirements, interpretation=options.interpretation,
                schema_inputs=inputs.schema_source, sql_inputs=inputs.sql_source, workspace=workspace / "build",
                cache=cache, approved_baseline=options.approved_baseline, schema_hash=inputs.schema_hash)
        except CompileError as error:
            raise Rejection("UNVERIFIED", str(error)) from error
        snapshot, generated = workspace / "bundle.ndjson", workspace / "generated.json"
        snapshot.write_bytes(bundle_bytes)
        generated.write_text(json.dumps(inputs.structural), encoding="utf-8")
        output = workspace / "gate-output"
        output.mkdir()
        checked = run_process(
            [str(runtime.bundle_checker), *map(str, runtime.libraries), str(contract.trusted), str(snapshot),
             str(generated)],
            write_root=output, environment={"LEAN_SYSROOT": str(runtime.sysroot)}, timeout=30)
    if checked.returncode == 2:
        raise Rejection("VIOLATED", "A kernel-checked argument refutes the supplied verification contract")
    if checked.returncode != 0:
        raise Rejection("UNVERIFIED", checked.stderr.strip() or "Bundle checker rejected the proof")
    hashes = {**contract.hashes, **inputs.hashes, "bundle": hashlib.sha256(bundle_bytes).hexdigest()}
    return {"status": "VERIFIED", "profile": inputs.profile.engine, "statements": inputs.statements,
            "inputs": hashes, "compiled_modules": list(compiled)}
