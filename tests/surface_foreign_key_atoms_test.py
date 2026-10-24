"""Public FK atoms distinguish row truth, parent compatibility and pragma preparation."""

from pathlib import Path
import re

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, surface_command

STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
"""Logical axioms admitted by the kernel audit; semantic assumptions are excluded."""

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


@pytest.mark.parametrize("fixture,axioms", [("ForeignKeyAtoms.lean", 14), ("ForeignKeyComparison.lean", 6)])
def test_independent_foreign_key_atoms(fixture: str, axioms: int, runtime_root: Path, tmp_path: Path) -> None:
    """ForeignKeyFacts, mapping transport and pragma laws compile through Belay's exported API.

    The fixture distinguishes both atoms, tests NULL and missing targets, repeated parent
    columns, affinity, rowid and NOCASE, and rejects an untransported child position after DROP.
    The comparison fixture checks structural lookup/scan agreement and a mixed-affinity
    counterexample. Every displayed law excludes native-computation or admission axioms.
    """
    result = run_command(surface_command(runtime_root, FIXTURES / fixture, tmp_path),
                         cwd=tmp_path, timeout=90)
    assert result.returncode == 0, result.diagnostic()
    reports = re.findall(r"depends on axioms: \[([^]]*)\]|does not depend on any axioms", result.stdout)
    assert len(reports) == axioms, result.diagnostic()
    for report in reports:
        assert set(filter(None, map(str.strip, report.split(",")))) <= STANDARD_AXIOMS, result.diagnostic()
