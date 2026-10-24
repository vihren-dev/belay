"""The isolated S6 prototype uses the existing SQL execution and S4 success laws."""

import json
from pathlib import Path
import re

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, module_setup

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_s6_transformer_agrees_with_execution(runtime_root: Path, tmp_path: Path) -> None:
    """The prototype WPMonad preserves bind, matches S4 success and proves actual-run
    postconditions. Concrete branches, errors, full-state counterexamples and both triple
    proof routes are checked; imported proofs use only the ordinary Lean logical axioms."""
    setup = module_setup(runtime_root, tmp_path)
    configuration = json.loads(setup.read_text())
    for module, count in (("S6Wp", 3), ("S6WpSoundness", 4), ("S6WpExamples", 12),
                          ("S6Equivalence", 6), ("S6Footprints", 3)):
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
            assert set(filter(None, map(str.strip, report.split(",")))) <= {
                "propext", "Classical.choice", "Quot.sound"
            }, result.diagnostic()
        configuration["importArts"][module] = [[str(artifact)]]
