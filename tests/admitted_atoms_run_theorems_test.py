"""The used Valid helpers preserve every execution with their stated entry assumptions.

The empty database and the equivalence with admitted constraint atoms keep their contracts.
"""

from pathlib import Path

import pytest

from tests.shared_table_shape_test import compile_checks

pytestmark = [pytest.mark.integration, pytest.mark.kernel,
              pytest.mark.requires_lean("compiler")]

THEOREMS = ["runScriptAllFrom_valid", "runScriptStep_valid", "Database.valid_empty", "Database.valid_iff"]

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
"""The axioms of Lean's logic that a proof of the model may use; any other axiom, such as
`sorryAx` or one that a proof adds, is refused."""


CHECKS = """
import Belay.Sqlite.Model
open Belay.Sqlite.Model
example {profile : Profile} (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value))
    (execution : context.mode = .execution) (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.Valid profile)) :
    ∀ run ∈ runScriptAllFrom context clock index connection script,
      run.connection.state.Holds (Database.Valid profile) :=
  runScriptAllFrom_valid context clock index script execution same holds
example {profile : Profile} (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (statement : Syntax.Statement) (values : List Value)
    (execution : context.mode = .execution) (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.Valid profile)) :
    ∀ found ∈ (runScriptStep context clock index connection statement values).executions,
      found.next.state.Holds (Database.Valid profile) :=
  runScriptStep_valid context clock index statement values execution same holds
example (profile : Profile) : (({} : Database)).Valid profile := Database.valid_empty profile
example {profile : Profile} {database : Database} :
    database.Valid profile ↔ database.AdmittedWith profile Database.ConstraintAtoms := Database.valid_iff
""" + "".join(f"#print axioms {name}\n" for name in THEOREMS)


def test_admitted_atoms_run_theorems(tmp_path: Path, lean_sysroot: Path,
                                     lean_libraries: tuple[Path, Path]) -> None:
    """The Valid helpers retain all-execution formulas and use only standard axioms."""
    output = compile_checks(CHECKS, tmp_path, lean_sysroot, lean_libraries)
    reports = [line for line in output.splitlines() if "depends on axioms" in line]
    assert len(reports) == len(THEOREMS), output
    for report in reports:
        axioms = report.split("[", 1)[1].rstrip("]").split(", ")
        assert set(axioms) <= STANDARD_AXIOMS, report
