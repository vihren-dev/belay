"""Independent NOT NULL, type and CHECK contracts use only standard axioms.

The shared write primitives and row-local formula retain their ADR25 migration witnesses.
The four temporary fixture files contain all 84 retired endpoint formulas once; remove them
after the execution-condition task's final Nix acceptance. Whole-statement contracts,
independent-premise checks and generic proof audits remain.
"""

from pathlib import Path

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
    "runSqlFrom_holds_ready",
    "runScriptAllFrom_holds_derived",
    "runScriptAllFrom_admittedWith",
]

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
"""The axioms of Lean's logic that a proof of the model may use; any other axiom, such as
`sorryAx` or one that a proof adds, is refused."""

CHECKS = """
import Belay.Sqlite.Model
open Belay.Sqlite.Model

-- ADR25 migration witnesses: keep through the final API/context contract change.
example {atom : Table → Prop} {database : Database} (every : database.EachTable atom)
    {target : Nat} {table : Table} (found : database.table target = some table) {rows : List Row}
    (stored : atom { table with rows }) : (database.setRows target rows).EachTable atom :=
  Database.Every.setRows (fact := fun _ _ table => atom table) every found stored
example {database : Database} (unique : database.KeysUnique) {target : Nat} {table : Table}
    (found : database.table target = some table) {rows : List Row}
    (stored : ({ table with rows } : Table).KeysUnique (database.catalog.uniqueKeys target table.shape)) :
    (database.setRows target rows).KeysUnique :=
  Database.Every.setRows (fact := fun catalog position table =>
    table.KeysUnique (catalog.uniqueKeys position table.shape)) unique found stored
example {atom : Table → Prop} (rowLocal : RowLocalAtom atom) {database : Database}
    (every : database.EachTable atom) {target : Nat} {table : Table} (found : database.table target = some table)
    (keys : List UniqueKey) (result : Table) (shape : result.shape = table.shape) :
    (checkedWrite database target keys result).Satisfies fun after => after.EachTable atom :=
  checkedWrite_satisfies every found keys result shape
    fun passed => rowLocal.constraints keys result (Bool.and_eq_true_iff.mp passed).1
example {atom : Table → Prop} (rowLocal : RowLocalAtom atom) {database : Database}
    (every : database.EachTable atom) {target : Nat} {table : Table} (found : database.table target = some table)
    (keys : List UniqueKey) (rows : List (List Value)) (result : Table) (shape : result.shape = table.shape) :
    (insertOutcome database target keys table rows result).Satisfies fun after => after.EachTable atom :=
  insertOutcome_satisfies every found keys rows result shape
    fun passed => rowLocal.constraints keys result (Bool.and_eq_true_iff.mp passed).1
example {atom : Table → Prop} (rowLocal : RowLocalAtom atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (statement : Resolved.Statement) {database : Database}
    (every : database.EachTable atom)
    (appended : ∀ target column refuses, statement = .addColumn target column refuses → ∀ table value,
      database.table target = some table → AddedCell table column value →
        atom (table.appendColumns [(column, value)])) :
    (runStatement clock counters parameters statement database).effect.Satisfies fun after => after.EachTable atom :=
  runStatement_rowLocal rowLocal clock counters parameters statement every appended
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
""" + "".join(f"#print axioms {name}\n" for name in THEOREMS)


def test_valid_atoms_theorems(tmp_path: Path, lean_sysroot: Path, lean_libraries: tuple[Path, Path]) -> None:
    """Independent atom contracts and general preservation evidence use only standard axioms."""
    output = compile_checks(CHECKS, tmp_path, lean_sysroot, lean_libraries)
    reports = [line for line in output.splitlines() if "depends on axioms" in line]
    assert len(reports) == len(THEOREMS), output
    for report in reports:
        axioms = report.split("[", 1)[1].rstrip("]").split(", ")
        assert set(axioms) <= STANDARD_AXIOMS, report


@pytest.mark.parametrize("fixture", [f"PreservationApiWitnesses{index}.lean" for index in range(1, 5)])
def test_preservation_api_migration(fixture: str, tmp_path: Path, lean_sysroot: Path,
                                    lean_libraries: tuple[Path, Path]) -> None:
    """Generic proofs derive all 84 pre-removal formulas until the final contract change."""
    source = Path(__file__).parent / "surface" / fixture
    compile_checks(source.read_text(), tmp_path, lean_sysroot, lean_libraries)
