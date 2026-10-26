import Belay
import Belay.Sqlite.Model.ForeignKeySelectedRuns

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! The run contracts for the selected mapping cover DROP, and the audit lists every theorem of the
selected-mapping contracts. DROP of the child meets its conditions; DROP of the parent does not and breaks
the row atom. CREATE TABLE and ADD COLUMN are in `ForeignKeyDdlRuns.lean`. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyDdlDropRunsFixture

/-- Two matching child rows make every preservation nonvacuous. -/
def input : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k));
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1),(1);"

/-- Both atoms hold on the input, under the mapping that its catalog selects. -/
theorem inputAtoms : input.raw.ParentSchemasCompatible input.raw.catalog.foreignKeyMapping ∧
    input.raw.RowReferencesHold input.raw.catalog.foreignKeyMapping := by decide +kernel

/-- A property of the database of a run that succeeds. A failed or open run does not have it. -/
def Succeeds (property : Model.Database → Prop) : Model.Outcome → Prop
  | .success database => property database
  | .failure .. => False
  | .pending .. => False

/-- Decide {name}`Succeeds` by the decision of the property, so that the kernel can check it. -/
instance (property : Model.Database → Prop) [DecidablePred property] :
    (outcome : Model.Outcome) → Decidable (Succeeds property outcome)
  | .success database => inferInstanceAs (Decidable (property database))
  | .failure .. => inferInstanceAs (Decidable False)
  | .pending .. => inferInstanceAs (Decidable False)

/-- A one-statement script reaches only that statement. -/
theorem single {condition : Resolved.Statement → Model.Database → Prop} {statement : Resolved.Statement}
    (met : condition statement input.raw) : RunConditionsWith condition 0 [(statement, [])] {database := input.raw} := by
  refine ⟨met, ?_⟩
  split <;> trivial

/-- Only the parent has no declaration, so every kept table has none when the child is dropped. -/
theorem keptHaveNone (position : Nat) (shape : CatalogTable) (found : input.raw.catalog.tableAt position = some shape)
    (kept : (!([1].contains position)) = true) : shape.allForeignKeys = [] := by
  have size : input.raw.catalog.length = 2 := by decide +kernel
  have bound : position < 2 := by
    unfold Catalog.tableAt at found
    cases present : input.raw.catalog[position]? with
    | none => simp [present] at found
    | some _ => exact size ▸ (List.getElem?_eq_some_iff.mp present).1
  have choice : position = 0 ∨ position = 1 := by omega
  rcases choice with rfl | rfl
  · have none : (input.raw.catalog.tableAt 0).map (·.allForeignKeys) = some [] := by decide +kernel
    rw [found] at none
    exact Option.some.inj none
  · simp at kept

/-- DROP of the child table keeps every declaration of the kept tables, of which there are none. -/
theorem dropChildCondition : (Resolved.Statement.drop [1] none).ForeignKeyAtomsCondition Profile.pinned input.raw :=
  ⟨fun position shape found kept key declared => absurd declared (by rw [keptHaveNone position shape found kept]; simp),
    fun position shape found kept key declared => absurd declared (by rw [keptHaveNone position shape found kept]; simp)⟩

/-- Both atoms hold after a fresh run of the DROP of the child. -/
theorem dropRun : (runSql [(.drop [1] none, [])] input.raw).Holds
    (fun result => result.ParentSchemasCompatible result.catalog.foreignKeyMapping ∧
      result.RowReferencesHold result.catalog.foreignKeyMapping) :=
  runSql_foreignKeyAtomsSelected Profile.pinned _ inputAtoms (single dropChildCondition)

/-- The run succeeds and leaves only the parent. -/
theorem dropRuns : Succeeds (fun result => result.catalog.length = 1) (runSql [(.drop [1] none, [])] input.raw) := by
  decide +kernel

/-- The DROP of the parent succeeds with enforcement off and leaves the child rows without a
parent, so the condition on kept parents is needed. -/
theorem dropParentBreaksRows : Succeeds (fun result => ¬ result.RowReferencesHold result.catalog.foreignKeyMapping)
    (runSql [(.drop [0] none, [])] input.raw) := by decide +kernel

end ForeignKeyDdlDropRunsFixture

#print axioms ForeignKeyDdlDropRunsFixture.inputAtoms
#print axioms ForeignKeyDdlDropRunsFixture.single
#print axioms ForeignKeyDdlDropRunsFixture.keptHaveNone
#print axioms ForeignKeyDdlDropRunsFixture.dropChildCondition
#print axioms ForeignKeyDdlDropRunsFixture.dropRun
#print axioms ForeignKeyDdlDropRunsFixture.dropRuns
#print axioms ForeignKeyDdlDropRunsFixture.dropParentBreaksRows
#print axioms Belay.Sqlite.Model.Database.ParentSchemasCompatible.selected
#print axioms Belay.Sqlite.Model.Database.ParentSchemasCompatible.createKeepsSelection
#print axioms Belay.Sqlite.Model.Database.AddColumnRowsCondition.keepsSelection
#print axioms Belay.Sqlite.Model.runStatement_create_rowReferencesSelected
#print axioms Belay.Sqlite.Model.runStatement_create_parentSchemasCompatibleSelected
#print axioms Belay.Sqlite.Model.runStatement_addColumn_rowReferencesSelected
#print axioms Belay.Sqlite.Model.runStatement_addColumn_parentSchemasCompatibleSelected
#print axioms Belay.Sqlite.Model.runStatement_drop_rowReferencesSelected
#print axioms Belay.Sqlite.Model.runStatement_drop_parentSchemasCompatibleSelected
#print axioms Belay.Sqlite.Model.runStatement_parentSchemasCompatibleSelected
#print axioms Belay.Sqlite.Model.runStatement_foreignKeyAtomsSelected
#print axioms Belay.Sqlite.Model.runStatement_rowReferences
#print axioms Belay.Sqlite.Model.parentSchemasCompatibleSelectedKeeps
#print axioms Belay.Sqlite.Model.runSqlFrom_parentSchemasCompatibleSelected
#print axioms Belay.Sqlite.Model.runSql_parentSchemasCompatibleSelected
#print axioms Belay.Sqlite.Model.runScriptAllFrom_parentSchemasCompatibleSelected
#print axioms Belay.Sqlite.Model.foreignKeyAtomsSelected_statementKeeps
#print axioms Belay.Sqlite.Model.runSqlFrom_foreignKeyAtomsSelected
#print axioms Belay.Sqlite.Model.runSql_foreignKeyAtomsSelected
#print axioms Belay.Sqlite.Model.runScriptAllFrom_foreignKeyAtomsSelected
