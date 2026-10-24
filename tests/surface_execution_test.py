"""Production SQL branches and weakest preconditions agree with the existing interpreter."""

import json
from pathlib import Path
import re

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, module_setup

ALLOWED_PROOF_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
"""Ordinary logical axioms; unchecked evaluation and assumed execution soundness are excluded."""

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_execution_branches_and_wp(runtime_root: Path, tmp_path: Path) -> None:
    """Installed production branches preserve full outcomes, validity and bind, including
    stopped prefixes and raw LIMIT wrappers. Their WPMonad proves a real write with two
    proof routes, rejects alternate stops, and preserves clocks, counters and snapshots.
    Success policies distinguish modeled errors from stops; fresh triples have exact
    ordinary-triple and universal S4 bridges without changing arbitrary-context triples."""
    setup = module_setup(runtime_root, tmp_path)
    configuration = json.loads(setup.read_text())
    for module, count in (("ExecutionBranches", 14), ("ExecutionProofs", 18), ("ExecutionSuccess", 22)):
        configuration["name"] = module
        setup.write_text(json.dumps(configuration))
        artifact = tmp_path / f"{module}.olean"
        result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup}",
                              "-R", str(FIXTURES), "-o", str(artifact),
                              str(FIXTURES / f"{module}.lean")], cwd=tmp_path, timeout=120)
        assert result.returncode == 0, result.diagnostic()
        reports = re.findall(r"depends on axioms: \[([^]]*)\]", result.stdout)
        assert len(reports) == count, result.diagnostic()
        for report in reports:
            assert set(filter(None, map(str.strip, report.split(",")))) <= ALLOWED_PROOF_AXIOMS, result.diagnostic()
        configuration["importArts"][module] = [[str(artifact)]]
