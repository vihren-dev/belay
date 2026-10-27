import Belay

/-! A fixture module of `tests/surface_s6_rules_test.py`: writes that the structural frame rule must not
cover, because they change more than their target table or more than the rows that a table frame sees
(ADR 0017, S6). A trigger and a foreign-key action write a second table. A generated column changes with its
base column. A rollback undoes writes to other tables. For each case, the fixture shows that the resolved
statement is not sheltered and that the frame claim that the rule would give is false: the actual run changes what
the frame observes. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace S6RulesNegativeFrames
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The first statement of a script. The scripts of this fixture have one statement each. -/
def firstStatement (script : Script) (nonempty : script.statements ≠ [] := by decide +kernel) : Syntax.Statement :=
  (script.statements.head nonempty).1

/-- Whether the statement resolves at the state to a statement that the shelter rule does not cover: not a plain
write to another table than the position, not a query and not a prepare error. -/
def shelterRefused (position : Nat) (state : ResolveState) (statement : Syntax.Statement) : Bool :=
  match resolveStatement runContext state statement with
  | .ok (.query _ _, _) | .ok (.prepareError _, _) => false
  | .ok (resolved, _) => !(resolved.plainWriteTarget.any (· != position))
  | .error _ => false

/-- If the check succeeds, the statement is not sheltered from the position at the state. Proof sketch: a
sheltered statement would make every successful resolution a plain write to another table, a query or a
prepare error, which the check excludes. -/
theorem shelterRefused_sound {position : Nat} {state : ResolveState} {statement : Syntax.Statement}
    (refused : shelterRefused position state statement = true) : ¬ statement.ShelteredAt position state := by
  intro sheltered
  unfold shelterRefused at refused
  split at refused
  · cases refused
  · cases refused
  · rename_i resolved after notQuery notPrepare found
    rcases sheltered resolved after found with ⟨target, plain, other⟩ | ⟨query, subqueries, same⟩ | ⟨error, same⟩
    · simp [plain, other] at refused
    · exact notQuery query subqueries same
    · exact notPrepare error same
  · cases refused

-- A trigger writes a second table.

/-- Two tables and a trigger that logs each new item. -/
def triggered : Database := db! r"
  CREATE TABLE items(id INTEGER PRIMARY KEY, qty INTEGER);
  CREATE TABLE audit(item INTEGER);
  CREATE TRIGGER items_audit AFTER INSERT ON items BEGIN INSERT INTO audit VALUES(NEW.id); END;"

/-- A complete environment with a constant clock. -/
def environment : Env :=
  { clock := some (fun _ => 0), counters := Counters.newConnection }

/-- The insert of an item. -/
def addItem : Script := sql r"INSERT INTO items VALUES(1, 5)"

/-- The insert is not sheltered from the audit table, which is at position 1: it has rules for the trigger. Proof
sketch: kernel evaluation of the check. -/
theorem trigger_not_sheltered :
    ¬ (firstStatement addItem).ShelteredAt 1 (ExecutionContext.initial triggered environment).connection.resolveState :=
  shelterRefused_sound (by decide +kernel)

/-- The frame claim of the shelter rule is false for the insert: the run changes the audit table. Proof sketch:
the actual run is a branch, and kernel evaluation shows that it adds a row to the table at position 1. -/
theorem trigger_changes_audit :
    ¬ (send addItem).Frame (fun connection => connection.state.database.table 1)
      (ExecutionContext.initial triggered environment) := by
  intro frame
  have same := frame _ (Sql.Branch.actual _ _ _ _)
  revert same
  decide +kernel

-- A foreign-key action writes a second table.

/-- A parent and a child table with a cascading delete. -/
def cascading : Database := db! r"
  CREATE TABLE parent(id INTEGER PRIMARY KEY);
  CREATE TABLE child(id INTEGER PRIMARY KEY, parent_id INTEGER REFERENCES parent(id) ON DELETE CASCADE);
  INSERT INTO parent VALUES(1);
  INSERT INTO child VALUES(1, 1);"

/-- Enable foreign keys, then delete the parent row. -/
def purgeParent : Script := sql r"PRAGMA foreign_keys = ON; DELETE FROM parent WHERE id = 1"

/-- The frame claim of the shelter rule is false for the program: the cascade empties the child table at
position 1. Proof sketch: kernel evaluation of the actual run. -/
theorem cascade_changes_child :
    ¬ (send purgeParent).Frame (fun connection => connection.state.database.table 1)
      (ExecutionContext.initial cascading environment) := by
  intro frame
  have same := frame _ (Sql.Branch.actual _ _ _ _)
  revert same
  decide +kernel

-- A generated column changes with its base column.

/-- A table with a stored generated column. -/
def generated : Database := db! r"
  CREATE TABLE g(id INTEGER PRIMARY KEY, b INTEGER, c INTEGER GENERATED ALWAYS AS (b * 2) STORED);
  INSERT INTO g(id, b) VALUES(1, 1);"

/-- The update of the base column. -/
def updateBase : Script := sql r"UPDATE g SET b = 5"

/-- The update changes the generated column, which it does not name: a frame on the cells of the target table
that it does not assign is false. Proof sketch: kernel evaluation of the cells of column 2 before and after. -/
theorem generated_cell_changes :
    ¬ (send updateBase).Frame
      (fun connection => (connection.state.database.rowsAt 0).map fun row => row.values.getD 2 .null)
      (ExecutionContext.initial generated environment) := by
  intro frame
  have same := frame _ (Sql.Branch.actual _ _ _ _)
  revert same
  decide +kernel

-- A rollback undoes the writes to other tables.

/-- The audit table with a transaction that has inserted a row. -/
def inTransaction : Connection :=
  (runScriptFrom runContext environment.clock 0
    ((ExecutionContext.initial triggered environment).connection)
    (sql r"BEGIN; INSERT INTO audit VALUES(7)").statements).connection

/-- The rollback of the open transaction. -/
def rollback : Script := sql r"ROLLBACK"

/-- The context inside the transaction. -/
def midTransaction : ExecutionContext :=
  { clock := environment.clock, index := 2, connection := inTransaction }

/-- The rollback is not sheltered from the audit table. Proof sketch: it is a transaction statement, not a
plain write, query or prepare error; kernel evaluation of the check. -/
theorem rollback_not_sheltered :
    ¬ (firstStatement rollback).ShelteredAt 1 midTransaction.connection.resolveState :=
  shelterRefused_sound (by decide +kernel)

/-- The frame claim of the shelter rule is false for the rollback: it removes the row that the transaction
inserted into the audit table. Proof sketch: kernel evaluation of the actual run. -/
theorem rollback_changes_audit :
    ¬ (send rollback).Frame (fun connection => connection.state.database.table 1) midTransaction := by
  intro frame
  have same := frame _ (Sql.Branch.actual _ _ _ _)
  revert same
  decide +kernel

#print axioms shelterRefused_sound
#print axioms trigger_not_sheltered
#print axioms trigger_changes_audit
#print axioms cascade_changes_child
#print axioms generated_cell_changes
#print axioms rollback_not_sheltered
#print axioms rollback_changes_audit

end S6RulesNegativeFrames
