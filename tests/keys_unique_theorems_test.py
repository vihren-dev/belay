"""The unique-key statement contract and lookup fact use only standard axioms.

The statement requires only uniqueness and its local condition. The lookup fact bounds
matching rows by one.
"""

from pathlib import Path

import pytest

from tests.shared_table_shape_test import compile_checks

pytestmark = [pytest.mark.integration, pytest.mark.kernel,
              pytest.mark.requires_lean("compiler")]

THEOREMS = [
    "runStatement_keysUnique",
    "Database.KeysUnique.lookup",
]

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
"""The axioms of Lean's logic that a proof of the model may use; any other axiom, such as
`sorryAx` or one that a proof adds, is refused."""

CHECKS = """
import Belay.Sqlite.Model
open Belay.Sqlite.Model
example (clock : Int) (counters : Counters) (parameters : List Value) (statement : Resolved.Statement)
    {database : Database} (unique : database.KeysUnique) (condition : statement.KeysCondition database) :
    (runStatement clock counters parameters statement database).effect.Satisfies Database.KeysUnique :=
  runStatement_keysUnique clock counters parameters statement unique condition
example {database : Database} (unique : database.KeysUnique) {position : Nat} {table : Table}
    (found : database.table position = some table) {key : UniqueKey}
    (member : key ∈ database.catalog.uniqueKeys position table.shape) (probe : Row) :
    (table.rows.filter fun row => LiteralData.keyEqual key row probe).length ≤ 1 :=
  Database.KeysUnique.lookup unique found member probe
""" + "".join(f"#print axioms {name}\n" for name in THEOREMS)


def test_keys_unique_theorems(tmp_path: Path, lean_sysroot: Path, lean_libraries: tuple[Path, Path]) -> None:
    """Each theorem of keys unique compiles with its formula and uses only propext, choice and quotients."""
    output = compile_checks(CHECKS, tmp_path, lean_sysroot, lean_libraries)
    reports = [line for line in output.splitlines() if "depends on axioms" in line]
    assert len(reports) == len(THEOREMS), output
    for report in reports:
        axioms = report.split("[", 1)[1].rstrip("]").split(", ")
        assert set(axioms) <= STANDARD_AXIOMS, report
