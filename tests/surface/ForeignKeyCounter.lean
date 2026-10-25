import Belay
import Belay.Sqlite.Model.ForeignKeyCounterRun
import Belay.Sqlite.Model.ForeignKeyCounterOld

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Counter-bound examples and the need for truthful raw update metadata. The resolved UPDATE
witness uses the public SQL surface; every proposition is checked by the kernel. -/

open Belay.Sqlite
open Belay.Sqlite.Model (KeyState KeyStop RowWork rowsKeys keyRun effectDatabase)

/-- A compatible parent and matching child, with enforcement enabled explicitly in later runs. -/
def matching : Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p);
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- Two orphan tables demonstrate that the total count is defined despite pragma order limits. -/
def twoOrphans : Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p); CREATE TABLE d(x REFERENCES p);
  INSERT INTO c VALUES(1); INSERT INTO d VALUES(2);"

example : matching.raw.foreignKeyViolations = 0 := by decide +kernel
example : twoOrphans.raw.foreignKeyViolations = 2 := by decide +kernel
example : twoOrphans.raw.foreignKeyCheckRows none = none := by decide +kernel
example : ({ rows := twoOrphans.raw.rows, counter := 2 } : KeyState).CounterBound twoOrphans.raw.catalog := by
  unfold KeyState.CounterBound
  decide +kernel
example : ¬ ({ rows := twoOrphans.raw.rows } : KeyState).CounterBound twoOrphans.raw.catalog := by
  unfold KeyState.CounterBound
  decide +kernel

/-- Raw work falsely claims that no column changes, while replacing the child's reference. -/
def uncheckedUpdate : RowWork :=
  .update 1 (fun row => { row with values := [.integer 9] }) [] [] [1] false

/-- The flexible raw engine trusts this metadata; it is not the resolved SQL frontend. -/
def uncheckedRun : Belay.Sqlite.Model.KeyRun := rowsKeys { depth := 0, keys := true } 0 1 uncheckedUpdate matching.raw true

/-- The raw update succeeds with one orphan, proving that changed-column coverage is necessary. -/
theorem uncheckedUpdateNeedsCoverage :
    uncheckedRun.effect = .ok (effectDatabase uncheckedRun.effect) ∧
      (effectDatabase uncheckedRun.effect).foreignKeyViolations = 1 := by decide +kernel

/-- A resolved UPDATE supplies the actual assigned and generated-column dependencies. -/
def resolvedRun : ScriptRun := matching.raw.run (sql "PRAGMA foreign_keys=ON; UPDATE c SET x=NULL;")

/-- The public UPDATE witness succeeds and keeps every row reference satisfied. -/
theorem resolvedUpdateChecksKeys : resolvedRun.outputs = [.done 0, .done 1] ∧
    resolvedRun.connection.state.database.foreignKeyViolations = 0 := by decide +kernel

/-- An input with valid row references starts with the required counter bound. -/
theorem matchingStart : ({ rows := matching.raw.rows } : KeyState).CounterBound matching.raw.catalog :=
  KeyState.CounterBound.start (by decide +kernel)

#print axioms Belay.Sqlite.Model.Database.foreignKeyViolations_zero
#print axioms KeyState.CounterBound.zero
#print axioms KeyState.CounterBound.start
#print axioms KeyState.CounterBound.of_rows_counter
#print axioms Belay.Sqlite.Model.keyRun_rowReferences
#print axioms Belay.Sqlite.Model.KeyResult.mapState_counterBound
#print axioms Belay.Sqlite.Model.NestedRun.credited_counterKeeps
#print axioms uncheckedUpdateNeedsCoverage
#print axioms resolvedUpdateChecksKeys

#print axioms Belay.Sqlite.Model.oldSteps_children_append
#print axioms Belay.Sqlite.Model.oldSteps_parents_counter
#print axioms Belay.Sqlite.Model.oldSteps_single_counter
#print axioms Belay.Sqlite.Model.oldSteps_counter_lower
