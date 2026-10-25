"""Execution views project real traces while retaining raw execution and continuation choices."""

import json
from pathlib import Path
import re

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, module_setup

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_execution_views_preserve_raw_context_and_branch_segments(runtime_root: Path, tmp_path: Path) -> None:
    """Installed view laws and kernel fixtures retain values, errors, stops, snapshots,
    counters and raw clock indices. Duplicate outputs and result-dependent raw/concrete
    alternatives use the descriptor's actual segment, including bind concatenation."""
    setup = module_setup(runtime_root, tmp_path)
    configuration = json.loads(setup.read_text())
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for module, count in (("ExecutionViews", 21), ("ExecutionViewBranches", 6)):
        configuration["name"] = module
        setup.write_text(json.dumps(configuration))
        artifact = tmp_path / f"{module}.olean"
        result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup}",
                              "-R", str(FIXTURES), "-o", str(artifact),
                              str(FIXTURES / f"{module}.lean")], cwd=tmp_path, timeout=120)
        assert result.returncode == 0, result.diagnostic()
        reports = re.findall(r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
        assert len(reports) == count, result.diagnostic()
        for report in reports:
            assert set(filter(None, map(str.strip, report.split(",")))) <= allowed, result.diagnostic()
        configuration["importArts"][module] = [[str(artifact)]]
