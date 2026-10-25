"""Projected comparison and migration domains reuse complete execution branches."""

import json
from pathlib import Path
import re

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, module_setup

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_migration_patterns_keep_original_domains_and_full_effects(runtime_root: Path, tmp_path: Path) -> None:
    """Installed view comparisons bridge ordinary execution, distinguish weak/full
    observations, and retain a moved migration failure inside its original domain.
    Kernel fixtures check values, counters, prefix errors, vacuity, raw-domain
    composition and independent clock/snapshot/step-count frame obligations."""
    setup = module_setup(runtime_root, tmp_path)
    configuration = json.loads(setup.read_text())
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for module, count in (("ExecutionViewComparisons", 15), ("ExecutionViewChoices", 5), ("MigrationPatterns", 12),
                          ("MigrationComposition", 16), ("ExecutionViewComposition", 20),
                          ("MigrationFrameBoundaries", 5)):
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
