import Belay
import Belay.Sqlite.Model.ForeignKeyRuns

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! Actual resolved and surface runs preserve the FK atoms outside their footprint,
including a partial FAIL and restoration of a saved snapshot. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyRunsFixture

/-- Real matching FK rows and a separate table whose uniqueness conflict uses FAIL. -/
def input : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k));
  CREATE TABLE aux(k UNIQUE ON CONFLICT FAIL);
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1); INSERT INTO aux VALUES(1);"

/-- The auxiliary table is neither a selected child nor a located parent. -/
theorem outside : input.raw.catalog.ForeignKeyOutside 2 := by
  intro link member
  change link ∈ [_] at member
  simp only [List.mem_singleton] at member
  subst link
  constructor
  · decide +kernel
  · intro parent key located
    cases located
    decide +kernel

/-- This write first inserts a new row, then fails at the preexisting unique value. -/
def partialWrite : Resolved.Statement :=
  .upsert 2 [[.value (.integer 2)], [.value (.integer 1)]] [] [] none [] none

/-- The fresh resolved-run law preserves both atoms through the actual partial FAIL. -/
theorem partialPreserves : (runSql [(partialWrite, [])] input.raw).Holds
    (fun result => result.ParentSchemasCompatible input.raw.catalog.foreignKeyMapping ∧
      result.RowReferencesHold input.raw.catalog.foreignKeyMapping) := by
  apply runSql_holds (foreignKeyAtoms_statementKeeps Profile.pinned _) _ (by decide +kernel)
  exact ⟨⟨by trivial, outside⟩, by trivial⟩

/-- The run really fails and retains the first inserted row, so the theorem is nonvacuous. -/
theorem partialRows : (match runSql [(partialWrite, [])] input.raw with
    | .failure 0 .constraintFail result => (result.rowsAt 2).map (·.values) = [[.integer 1], [.integer 2]]
    | _ => False) := by rfl

/-- A pending transaction has a modified auxiliary table and the matching original snapshot. -/
def transaction : SqlState :=
  { database := input.raw.setRows 2 [], snapshot := some input.raw }

/-- Both independent atoms on both stores suffice for the public rollback run law. -/
theorem rollbackPreserves : (runSqlFrom 4 [(.rollback, [])] transaction).Holds
    (fun result => result.ParentSchemasCompatible input.raw.catalog.foreignKeyMapping ∧
      result.RowReferencesHold input.raw.catalog.foreignKeyMapping) := by
  apply runSqlFrom_holds (foreignKeyAtoms_statementKeeps Profile.pinned _) 4 _
  · constructor
    · decide +kernel
    · intro snapshot same
      cases same
      decide +kernel
  · exact ⟨⟨True.intro, True.intro⟩, by trivial⟩

/-- Rollback restores the snapshot, including the auxiliary row removed from the current view. -/
theorem rollbackRestores : runSqlFrom 4 [(.rollback, [])] transaction = .success input.raw := by rfl

/-- The same valid current view with an orphaned saved snapshot illustrates the entry requirement. -/
def badSnapshot : SqlState :=
  { database := input.raw, snapshot := some (input.raw.setRows 0 []) }

/-- Current row truth alone cannot justify rollback: the restored snapshot has an orphan. -/
theorem snapshotRequired : badSnapshot.database.RowReferencesHold badSnapshot.database.catalog.foreignKeyMapping ∧
    ¬(runSqlFrom 0 [(.rollback, [])] badSnapshot).Holds
      (fun result => result.RowReferencesHold result.catalog.foreignKeyMapping) := by decide +kernel

/-- A plain surface INSERT outside the footprint runs with the normal enforcement-off connection. -/
def script : Script := sql "INSERT INTO aux VALUES(2);"

/-- The connection starts without an open transaction. -/
def connection : Connection := { state := {database := input.raw} }

/-- Successful resolution supplies the plain INSERT condition; the script has no later statement. -/
theorem scriptConditions : ScriptConditionsWith
    (fun statement database => statement.KeepsParentSchema ∧ statement.ForeignKeyRowsCondition Profile.pinned database)
    runContext none 0 connection script.statements := by
  constructor
  · intro resolved after equal
    change Except.ok (.upsert 2 [[.value (.integer 2)]] [] [] none [] none, connection.resolveState) = .ok (resolved, after) at equal
    cases equal
    exact ⟨by trivial, outside⟩
  · exact fun execution _ => trivial

/-- The public surface-run theorem preserves both atoms after a real parsed statement. -/
theorem scriptPreserves : ∀ run ∈ runScriptAllFrom runContext none 0 connection script.statements,
    run.connection.state.Holds
    (fun result => result.ParentSchemasCompatible input.raw.catalog.foreignKeyMapping ∧
      result.RowReferencesHold input.raw.catalog.foreignKeyMapping) := by
  apply runScriptAllFrom_holds (foreignKeyAtoms_statementKeeps Profile.pinned _) runContext none 0 _
  · exact ⟨by decide +kernel, fun _ same => nomatch same⟩
  · exact scriptConditions

/-- The surface run succeeds and stores the new row instead of merely satisfying an error branch. -/
theorem scriptRows : (runScriptFrom runContext none 0 connection script.statements).outputs = [.done 1] ∧
    ((runScriptFrom runContext none 0 connection script.statements).connection.state.database.rowsAt 2).map (·.values) =
      [[.integer 1], [.integer 2]] := by exact ⟨rfl, rfl⟩

end ForeignKeyRunsFixture

#print axioms ForeignKeyRunsFixture.outside
#print axioms ForeignKeyRunsFixture.partialPreserves
#print axioms ForeignKeyRunsFixture.partialRows
#print axioms ForeignKeyRunsFixture.rollbackPreserves
#print axioms ForeignKeyRunsFixture.rollbackRestores
#print axioms ForeignKeyRunsFixture.snapshotRequired
#print axioms ForeignKeyRunsFixture.scriptConditions
#print axioms ForeignKeyRunsFixture.scriptPreserves
#print axioms ForeignKeyRunsFixture.scriptRows
