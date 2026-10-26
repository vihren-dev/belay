"""The simulation syntax and its explanation (ADR 0017, S8)."""

from pathlib import Path
import re

import pytest

from tests.runtime_support import run_command
from tests.surface_assertion_examples_test import ALLOWED_PROOF_AXIOMS
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_simulation_syntax_elaborates_to_the_claims_and_explains_the_difference(runtime_root: Path,
                                                                                tmp_path: Path) -> None:
    """The syntax of ApplicationSyntax elaborates each of its forms to the public claim that it names
    (Simulation, or ScopedClaim with a relation), the guard becomes the context predicate, and the
    actual #explain command tells the two claims apart: the full-state claim compares complete final
    contexts, and the scoped claim names the relation and never claims equal final contexts."""
    result = run_command(surface_command(runtime_root, FIXTURES / "ApplicationSyntaxExamples.lean", tmp_path),
                         cwd=tmp_path, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    reports = re.findall(r"depends on axioms: \[([^]]*)\]", result.stdout)
    assert len(reports) == 3, result.diagnostic()
    for report in reports:
        assert set(filter(None, map(str.strip, report.split(",")))) <= ALLOWED_PROOF_AXIOMS, result.diagnostic()
    for written in ("migration simulates samePairing", "migration simulates samePairing where sqlGuard",
                    "migration simulates samePairing scoped by sameClock",
                    "migration simulates samePairing scoped by sameClock where sqlGuard"):
        assert f"Claim: {written}\n" in result.stdout, result.diagnostic()
    assert result.stdout.count("Full-state simulation claim.") == 2, result.diagnostic()
    assert result.stdout.count("Scoped simulation claim.") == 2, result.diagnostic()
    assert result.stdout.count("complete final connection, clock and raw next-statement index exactly") == 2
    assert result.stdout.count("Context relation: sameClock.") == 2, result.diagnostic()
    assert result.stdout.count("Admitted contexts: every execution context") == 2, result.diagnostic()
    assert result.stdout.count("Holds.inContext sqlGuard context") == 2, result.diagnostic()
    assert result.stdout.count("never claims that the final contexts are equal") == 2, result.diagnostic()
    assert "sorryAx" not in result.stdout, result.diagnostic()


@pytest.mark.parametrize("claim,at,message", [
    ('#check (Sql.pure ()) simulates (1 : Nat)', "(1 : Nat)", "type mismatch"),
    ('#check (Sql.pure ()) simulates pairing where sql r"DELETE FROM t"', 'sql r"DELETE', "one read-only statement"),
    ('#check (Sql.pure ()) simulates pairing scoped by 5', "5", "failed to synthesize"),
    ('#explain (Sql.pure ()) simulates pairing scoped by (fun a b => a = b) where sql r"SELECT 1; SELECT 2"',
     'sql r"SELECT', "one read-only statement"),
])
def test_simulation_syntax_reports_mistakes_where_they_are_written(
    runtime_root: Path, tmp_path: Path, claim: str, at: str, message: str,
) -> None:
    """The simulation syntax reports a non-pairing, a guard that is not one read-only query, and a
    relation that is not a relation, each at its own source position, and #explain explains nothing
    for a claim that does not elaborate."""
    source = tmp_path / "SimulationFailure.lean"
    source.write_text("import Belay\nopen Belay.Sqlite Belay.Sqlite.Calls\n"
                      "def pairing : Pairing ({ Argument := fun _ => Unit, Result := fun _ => Unit } : "
                      "Signature Unit) := ⟨fun _ => { script := fun _ => sql r\"SELECT 1\", result := fun _ => () },"
                      " fun _ => { script := fun _ => sql r\"SELECT 1\", result := fun _ => () }⟩\n"
                      f"{claim}\n")
    result = run_command(surface_command(runtime_root, source, tmp_path), cwd=tmp_path, timeout=120)
    assert result.returncode != 0, result.diagnostic()
    assert message.lower() in result.stdout.lower(), result.diagnostic()
    assert f":4:{claim.index(at)}:" in result.stdout, result.diagnostic()
    assert "Full-state simulation claim" not in result.stdout, result.diagnostic()
