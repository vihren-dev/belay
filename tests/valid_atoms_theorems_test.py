"""Independent NOT NULL, type and CHECK contracts use only standard axioms.

Whole-statement contracts, independent-premise checks and generic proof audits protect
support-independent atoms, actual evaluator inputs, halted suffixes and counter knowledge.
"""

from pathlib import Path
import re

import pytest

from tests.shared_table_shape_test import compile_checks

pytestmark = [pytest.mark.integration, pytest.mark.kernel,
              pytest.mark.requires_lean("compiler")]

THEOREMS = [
    "Database.Every.setRows",
    "checkedWrite_satisfies",
    "insertOutcome_satisfies",
    "runStatement_rowLocal",
    "Table.notNullAtom",
    "Table.typesFitAtom",
    "Table.checksHoldAtom",
    "runStatement_notNull",
    "runStatement_typesFit",
    "runStatement_checksHold",
    "StatementKeeps.ofOwnRun",
    "StatementKeeps.and",
    "RunConditionsWith.with_ready",
    "ScriptConditionsWith.of_invariant",
    "runScriptAllFrom_holds_derived",
    "runScriptFrom_holds",
    "runSqlFrom_holds",
    "runScriptAllFrom_holds",
    "runScriptAllFrom_admittedWith",
]

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
"""The axioms of Lean's logic that a proof of the model may use; any other axiom, such as
`sorryAx` or one that a proof adds, is refused."""

CHECKS = """
import Belay.Sqlite.Model
open Belay.Sqlite.Model

example (clock : Int) (counters : Counters) (parameters : List Value) (statement : Resolved.Statement)
    {database : Database} (holds : Database.NotNull database) (condition : statement.NotNullCondition database) :
    (runStatement clock counters parameters statement database).effect.Satisfies Database.NotNull :=
  runStatement_notNull clock counters parameters statement holds condition
example (clock : Int) (counters : Counters) (parameters : List Value) (statement : Resolved.Statement)
    {database : Database} (holds : Database.TypesFit database) (condition : statement.TypesFitCondition database) :
    (runStatement clock counters parameters statement database).effect.Satisfies Database.TypesFit :=
  runStatement_typesFit clock counters parameters statement holds condition
example (clock : Int) (counters : Counters) (parameters : List Value) (statement : Resolved.Statement)
    {database : Database} (holds : Database.ChecksHold database) (condition : statement.ChecksHoldCondition database) :
    (runStatement clock counters parameters statement database).effect.Satisfies Database.ChecksHold :=
  runStatement_checksHold clock counters parameters statement holds condition

-- Lasting boundary checks: actual input selection, halted suffixes and counter knowledge.
def inputRead : Resolved.Statement := .query
  { sources := [], filter := none, aggregate := false, groupBy := [],
    columns := [.scalar (.counter .changes), .scalar (.parameter 1)],
    names := ["changes", "parameter"], orderBy := [], offset := 0, limit := none } []
def inputState : SqlState where
  database := {}
  clock := fun index => index + 10
  counters := { changes := some 7, totalChanges := some 9, lastInsertRowid := some 11 }
def exactInputs : StatementCondition := fun clock counters parameters _ _ =>
  clock = 17 ∧ counters = { changes := some 7 } ∧ parameters = [.integer 42]
example : RunConditionsWith exactInputs 7 [(inputRead, [.integer 42])] inputState :=
  ⟨⟨rfl, rfl, rfl⟩, trivial⟩
example : (runSqlFrom 7 [(inputRead, [.integer 42])] inputState).Holds Database.RowsShaped :=
  runSqlFrom_holds (condition := exactInputs)
    (fun clock counters parameters statement database holds _ =>
      rowsShaped_statementKeeps clock counters parameters statement database holds trivial)
    7 _ ⟨by decide +kernel, fun _ impossible => nomatch impossible⟩ ⟨⟨rfl, rfl, rfl⟩, trivial⟩
-- Rollback without a transaction halts before BEGIN, whose hypothetical condition is false.
example : RunConditionsWith (fun _ _ _ statement _ => statement = .rollback)
    4 [(.rollback, []), (.begin, [])] { database := {} } := ⟨rfl, trivial⟩
-- A raw query can be ready while the state refuses an unknown counter read.
example : (runStatement 0 {} [] inputRead {}).ready = true ∧
    (({ database := {} } : SqlState).statementRun 0 [] inputRead).ready = false := ⟨rfl, rfl⟩
example {property : Database → Prop} {condition : StatementCondition}
    (keeps : StatementKeeps property condition) (position : Nat)
    (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds property) (met : RunConditionsWith condition position script state) :
    (runSqlFrom position script state).Holds property := runSqlFrom_holds keeps position script holds met
example {property : Database → Prop} {condition : StatementCondition}
    (keeps : StatementKeeps property (fun clock counters parameters statement database =>
      condition clock counters parameters statement database ∧
      (runStatement clock counters parameters statement database).ready = true))
    (position : Nat) (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds property) (met : RunConditionsWith condition position script state)
    (supported : supportedSqlFrom position script state = true) : (runSqlFrom position script state).Holds property :=
  runSqlFrom_holds keeps position script holds (RunConditionsWith.with_ready position script state met supported)
""" + "".join(f"#print axioms {name}\n" for name in THEOREMS)


def test_valid_atoms_theorems(tmp_path: Path, lean_sysroot: Path, lean_libraries: tuple[Path, Path]) -> None:
    """Independent atom contracts and general preservation evidence use only standard axioms."""
    output = compile_checks(CHECKS, tmp_path, lean_sysroot, lean_libraries)
    reports = re.findall(r"depends on axioms: \[([^]]*)\]|does not depend on any axioms", output)
    assert len(reports) == len(THEOREMS), output
    for report in reports:
        assert set(filter(None, map(str.strip, report.split(",")))) <= STANDARD_AXIOMS, report

