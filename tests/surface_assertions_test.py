"""Fresh-run claims, query assertions and their explanations agree with existing execution."""

import json
from pathlib import Path
import re

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, module_setup, surface_command

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


def test_fresh_notation_expands_to_primitives(runtime_root: Path, tmp_path: Path) -> None:
    """The installed ensures notation expands to FreshEnsures for scripts, programs, bound values and
    guards, equals the success notation, and reports an invalid guard at its source."""
    result = run_command(surface_command(runtime_root, FIXTURES / "FreshNotationExamples.lean", tmp_path),
                         cwd=tmp_path, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    reports = axiom_reports(result.stdout)
    assert len(reports) == 4, result.diagnostic()
    for report in reports:
        assert report <= ALLOWED_PROOF_AXIOMS, result.diagnostic()
    assert "sorryAx" not in result.stdout, result.diagnostic()


def test_explain_describes_fresh_ordinary_and_success_claims(runtime_root: Path, tmp_path: Path) -> None:
    """The actual #explain command states entry assumptions, the captured start, the error policy and
    the observation context of fresh, ordinary and success claims, without an invented meaning."""
    result = run_command(surface_command(runtime_root, FIXTURES / "ClaimExplanationExamples.lean", tmp_path),
                         cwd=tmp_path, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    expected = {
        "Fresh-run claim.": 5, "Ordinary triple.": 1, "Success claim.": 1,
        "Every permitted branch must return a value and stay modeled": 6,
        "The initial database is captured once and stays fixed": 5,
        "Error policy andOk:": 3, "Error policy ifOk:": 1, "Error policy: neither ifOk nor andOk": 2,
        "makes the claim false": 1,
        "Default query assertions (Holds, holds)": 4, "holdsInContext reads the actual clock": 1,
        "The claim states no query assertion.": 2, "is not a fresh-run claim": 1,
    }
    for text, count in expected.items():
        assert result.stdout.count(text) == count, f"{text!r}\n{result.diagnostic()}"
    for written in ('((Sql.pure 1) succeeds where sql r"SELECT 1")',
                    '((Sql.pure 1) ensures ifOk (holds (sql r"SELECT 1")))'):
        assert f"Claim: {written}" in result.stdout, result.diagnostic()
    assert "sorryAx" not in result.stdout, result.diagnostic()


@pytest.mark.parametrize(("claim", "at", "message"), [
    ('#check ((Sql.pure ()) ensures andOk ⌜True⌝ where sql r"DELETE FROM t")', 'sql r"DELETE',
     "one read-only statement"),
    ('#explain ((Sql.pure ()) ensures andOk ⌜True⌝ where sql r"SELECT 1; SELECT 2")', 'sql r"SELECT',
     "one read-only statement"),
    ('#check holds (sql r"DELETE FROM t")', "holds (sql", "one read-only statement"),
    ('#check holdsInContext (sql r"SELECT 1; SELECT 2")', "holdsInContext (sql", "one read-only statement"),
    ('#explain (1 = 1)', "(1 = 1)", "Cannot explain this proposition"),
])
def test_assertion_diagnostics_reject_unadmitted_input(
    runtime_root: Path, tmp_path: Path, claim: str, at: str, message: str,
) -> None:
    """Fresh notation and both assertion terms report a query that is not one read-only statement at
    its source, and #explain reports an unsupported proposition instead of inventing a meaning."""
    source = tmp_path / "AssertionFailure.lean"
    source.write_text(f"import Belay\nopen Belay.Sqlite Std.Do\n{claim}\n")
    result = run_command(surface_command(runtime_root, source, tmp_path), cwd=tmp_path, timeout=120)
    assert result.returncode != 0, result.diagnostic()
    assert message.lower() in result.stdout.lower(), result.diagnostic()
    assert f":3:{claim.index(at)}:" in result.stdout, result.diagnostic()
    assert "Fresh-run claim." not in result.stdout, result.diagnostic()
