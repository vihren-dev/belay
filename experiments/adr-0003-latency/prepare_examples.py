"""Keep the production compiler's trusted and candidate `.olean` outputs for each example.

Usage: python3 experiments/adr-0003-latency/prepare_examples.py
Writes build/adr-0003-latency/compiled/<case>/{trusted,candidate}.
"""

import argparse
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cases import CASES, ROOT, WORK  # noqa: E402

sys.path.insert(0, str(ROOT))
from migration_check.compile import compile_project  # noqa: E402
from migration_check.inputs import generated_inputs  # noqa: E402


def compile_case(name: str, schema: Path, approved: Path, candidate: Path, version: str) -> Path:
    """Run the same staged compilation as `verify`, into a workspace that is kept."""
    inputs = generated_inputs(argparse.Namespace(profile=version, schema=schema,
                                                 migration=candidate / "migration.sql"))
    runtime = inputs.runtime
    workspace = WORK / "compiled" / name
    shutil.rmtree(workspace, ignore_errors=True)
    workspace.mkdir(parents=True)
    compile_project(sysroot=runtime.sysroot, libraries=runtime.libraries,
                    requirements=approved / "Requirements.lean", interpretation=approved / "Interpretation.lean",
                    next_interpretation=candidate / "NextInterpretation.lean", proofs=candidate / "Proofs.lean",
                    schema_inputs=inputs.schema_source, sql_inputs=inputs.sql_source,
                    workspace=workspace)
    return workspace


if __name__ == "__main__":
    for case in CASES:
        print(compile_case(case.name, case.schema, case.approved, case.candidate, case.profile))
