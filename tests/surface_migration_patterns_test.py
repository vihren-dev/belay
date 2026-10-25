"""Projected comparison and migration domains reuse complete execution branches."""

import json
from pathlib import Path
import re

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, module_setup, surface_command

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
                          ("MigrationFrameBoundaries", 5), ("MigrationApplicationComposition", 14)):
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


def test_pattern_syntax_explains_checked_primitives(runtime_root: Path, tmp_path: Path) -> None:
    """MigrationPatternSyntax expands all eight forms, bound values and quiet descriptors;
    the actual #explain command distinguishes weak/full scope and original-success vacuity."""
    result = run_command(surface_command(runtime_root, FIXTURES / "MigrationPatternSyntaxExamples.lean", tmp_path),
                         cwd=tmp_path, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    reports = re.findall(r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    assert len(reports) == 10, result.diagnostic()
    for report in reports:
        assert set(filter(None, map(str.strip, report.split(",")))) <= {
            "propext", "Classical.choice", "Quot.sound"}, result.diagnostic()
    assert result.stdout.count("every complete fresh environment") == 4, result.diagnostic()
    assert result.stdout.count("that instance is vacuous") == 4, result.diagnostic()
    assert result.stdout.count("not the comparison environment") == 4, result.diagnostic()
    assert result.stdout.count("Final connection state, clock and next index are omitted") == 2, result.diagnostic()
    assert result.stdout.count("including counters and transaction snapshots") == 2, result.diagnostic()
    assert result.stdout.count("cannot remove the original context from the domain") == 2, result.diagnostic()
    assert result.stdout.count("Retain errors, unmodeled stops and partial traces") == 4, result.diagnostic()
    for written in (
        'migration preserves sql r"SELECT 1" where sqlGuard',
        'migration translates sql r"SELECT 1" to sql r"SELECT 2"',
        '(Sql.pure 7) commutes with migration',
        '(Sql.pure 7) commutes with migration as (Sql.pure 8) where sqlGuard',
    ):
        assert f"Claim: {written}" in result.stdout, result.diagnostic()
    assert "Model.Syntax.Statement" not in result.stdout, result.diagnostic()
    assert "sorryAx" not in result.stdout, result.diagnostic()


@pytest.mark.parametrize(("claim", "at", "message"), [
    ('#check ((Sql.pure ()) preserves sql r"DELETE FROM t")', 'sql r"DELETE', "one read-only statement"),
    ('#check ((Sql.pure ()) translates sql r"SELECT 1" to sql r"DELETE FROM t")',
     'sql r"DELETE', "one read-only statement"),
    ('#check ((Sql.pure 1) commutes with (Sql.pure ()) where sql r"SELECT 1; SELECT 2")',
     'sql r"SELECT', "one read-only statement"),
    ('#explain True', "True", "Cannot explain this proposition"),
    ('#explain (Sql.pure ()) preserves sql r"DELETE FROM t"', 'sql r"DELETE', "one read-only statement"),
    ('#check (do quiet (Sql.pure ()); pure 1 : Sql Nat)', "quiet", "type mismatch"),
])
def test_pattern_diagnostics_reject_unadmitted_claims(
    runtime_root: Path, tmp_path: Path, claim: str, at: str, message: str,
) -> None:
    """Pattern admission reports the failing query/guard source, unsupported explanations
    report the claim, and quiet cannot silently become an executable Sql action."""
    source = tmp_path / "PatternFailure.lean"
    source.write_text(f"import Belay\nopen Belay.Sqlite\n{claim}\n")
    result = run_command(surface_command(runtime_root, source, tmp_path), cwd=tmp_path, timeout=120)
    assert result.returncode != 0, result.diagnostic()
    assert message.lower() in result.stdout.lower(), result.diagnostic()
    if claim.startswith("#explain"):
        assert "For every valid bundled database" not in result.stdout, result.diagnostic()
    if at != "quiet":
        assert f":3:{claim.index(at)}:" in result.stdout, result.diagnostic()
