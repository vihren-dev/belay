"""Fresh-run claims, query assertions and their explanations agree with existing execution."""

import json
from pathlib import Path
import re

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, module_setup

ALLOWED_PROOF_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
"""Ordinary logical axioms; unchecked evaluation and assumed execution soundness are excluded."""

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def axiom_reports(stdout: str) -> list[set[str]]:
    """The axiom sets of all `#print axioms` reports in the output of one Lean run."""
    reports = re.findall(r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", stdout)
    return [set(filter(None, map(str.strip, report.split(",")))) for report in reports]


def test_assertion_kernel_fixtures(runtime_root: Path, tmp_path: Path) -> None:
    """Context observations, fresh composition rules and assertion policies are proved against the
    existing execution implementation. The real-context and default assertions disagree on a clock,
    on counters and on a pragma setting, the default one follows rollback and open transactions, and
    neither a default assertion nor a fresh claim fixes the entry of an ordinary triple. The policies
    cover errors and unmodeled stops before and in the program, every oneOf choice and returned outputs."""
    setup = module_setup(runtime_root, tmp_path)
    configuration = json.loads(setup.read_text())
    for module, count in (("AssertionContexts", 12), ("FreshAssertionRules", 6), ("AssertionPolicies", 9)):
        configuration["name"] = module
        setup.write_text(json.dumps(configuration))
        artifact = tmp_path / f"{module}.olean"
        result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup}",
                              "-R", str(FIXTURES), "-o", str(artifact),
                              str(FIXTURES / f"{module}.lean")], cwd=tmp_path, timeout=120)
        assert result.returncode == 0, result.diagnostic()
        reports = axiom_reports(result.stdout)
        assert len(reports) == count, result.diagnostic()
        for report in reports:
            assert report <= ALLOWED_PROOF_AXIOMS, result.diagnostic()
        configuration["importArts"][module] = [[str(artifact)]]
