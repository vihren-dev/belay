"""`init`: create a proofs project around a candidate's Lean files (ADR 0010 section 1).

The project gets a starting `lakefile.toml` that reads the approved contract in
place, lists the generated and candidate modules, and requires the verifier's
library through `.belay/runtime`; a `lean-toolchain` with the pinned toolchain; and
the link itself. After that, `lake build` and the editor's Lean server work on the
project without the verifier. The lakefile belongs to the user from then on.
"""

import argparse
import os
from pathlib import Path
from tempfile import TemporaryDirectory

from .diagnostics import Rejection
from .prepare import discover_project
from .proofs_project import link_runtime, project_lakefile
from .runtime import Runtime
from .source_closure import CompileError

PACKAGE_NAME = "proofs"
"""Lake package name of a proofs project."""


def init_project(options: argparse.Namespace) -> dict[str, object]:
    """Write the starting lakefile, the toolchain file and the runtime link into `--project`."""
    runtime = Runtime.locate()
    project = options.project.resolve(strict=True)
    lakefile = project / "lakefile.toml"
    if lakefile.exists():
        raise Rejection("INPUT_ERROR", f"{lakefile} already exists; edit it, or remove it to create a new one")
    requirements, interpretation = options.requirements.resolve(strict=True), options.interpretation.resolve(strict=True)
    if requirements.parent != interpretation.parent:
        raise Rejection("INPUT_ERROR", f"{requirements} and {interpretation} are in different folders; "
                        "keep the approved contract in one folder, which the project reads in place")
    with TemporaryDirectory(prefix="init-") as temporary:
        try:
            contract, candidates, _ = discover_project(runtime=runtime, requirements=requirements,
                                                       interpretation=interpretation, project=project,
                                                       workspace=Path(temporary))
        except CompileError as error:
            raise Rejection("INPUT_ERROR", str(error)) from error
    lakefile.write_text(project_lakefile(PACKAGE_NAME, os.path.relpath(requirements.parent, project),
                                         contract.order, candidates), encoding="utf-8")
    (project / "lean-toolchain").write_text((runtime.root / "lean-toolchain").read_text(encoding="utf-8"),
                                           encoding="utf-8")
    link_runtime(project, runtime.root)
    return {"status": "INITIALIZED", "project": str(project), "lakefile": str(lakefile)}
