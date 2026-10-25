import Belay
import Belay.Sqlite.Model.ForeignKeySelectedRuns

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! The run contracts for the selected mapping cover the schema statements. Each form of CREATE,
ADD COLUMN and DROP runs through {lit}`runSql` with its own condition, and each condition is
needed: a statement that does not meet it breaks an atom. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyDdlRunsFixture

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
  | _ => False

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

/-- The child shape that the input declares, reused for a new child table. -/
def child : CatalogTable := (input.raw.catalog.tableAt 1).getD {columns := []}

/-- CREATE TABLE of a second child of the parent, at the end of the catalog. -/
def created : Resolved.Statement := .createTable 2 (.ofString "d") child

/-- The new declaration has a located parent, the only condition of CREATE TABLE for both atoms. -/
theorem createCondition : created.ForeignKeyAtomsCondition Profile.pinned input.raw := by
  intro shape entry key declared
  cases entry
  change key ∈ [_] at declared
  simp only [List.mem_singleton] at declared
  subst key
  decide +kernel

/-- Both atoms hold after a fresh run of the CREATE TABLE. -/
theorem createRun : (runSql [(created, [])] input.raw).Holds
    (fun result => result.ParentSchemasCompatible result.catalog.foreignKeyMapping ∧
      result.RowReferencesHold result.catalog.foreignKeyMapping) :=
  runSql_foreignKeyAtomsSelected Profile.pinned _ inputAtoms (single createCondition)

/-- The run succeeds, adds the table and keeps both original child rows. -/
theorem createRuns : Succeeds (fun result => result.catalog.length = 3 ∧ (result.rowsAt 1).length = 2)
    (runSql [(created, [])] input.raw) := by decide +kernel

/-- The shape of a table whose declaration references an absent parent. -/
def forwardShape : CatalogTable :=
  {child with columns := child.columns.map fun column =>
    {column with foreignKeys := column.foreignKeys.map fun key => {key with table := .ofString "missing"}}}

/-- CREATE TABLE of a table that references an absent parent. -/
def forward : Resolved.Statement := .createTable 2 (.ofString "forward") forwardShape

/-- The row-only contract needs only that old declarations keep their parents, which compatible
parent schemas give for every object. The new table has no rows. -/
theorem forwardRowsRun : (runSql [(forward, [])] input.raw).Holds
    (fun result => result.RowReferencesHold result.catalog.foreignKeyMapping) :=
  runSql_rowReferences Profile.pinned _ inputAtoms.2 (single (inputAtoms.1.createKeepsSelection _))

/-- The atoms contract refuses the forward reference, because its new declaration has no located
parent. -/
theorem forwardIsOutsideAtoms : ¬ forward.ForeignKeyAtomsCondition Profile.pinned input.raw := by
  intro condition
  have all : ∀ key ∈ forwardShape.allForeignKeys, ((input.raw.catalog ++
      [({name := .ofString "forward", entry := .table forwardShape} : CatalogObject)]).parentLink key).isLocated = true :=
    condition forwardShape rfl
  revert all
  decide +kernel

/-- The forward reference does run: it keeps row truth and breaks parent-schema compatibility. -/
theorem forwardBreaksSchema : Succeeds (fun result => result.RowReferencesHold result.catalog.foreignKeyMapping ∧
    ¬ result.ParentSchemasCompatible result.catalog.foreignKeyMapping) (runSql [(forward, [])] input.raw) := by
  decide +kernel

/-- The default 99. -/
def numberDefault : ColumnDefault :=
  { form := .literal (.value (.integer 99)) (.integer 99), sourceText := "99" }

/-- A column without constraints. -/
def plainColumn : CatalogColumn := {name := .ofString "y", declaredType := none}

/-- The declaration of a reference to the column {lit}`k` of the parent. -/
def parentReference : ForeignKey :=
  {table := .ofString "p", columns := [1], referenced := [.ofString "k"], onDelete := .noAction, onUpdate := .noAction}

/-- A column that references the parent and has the default 99, for which the parent has no row. -/
def numberColumn : CatalogColumn :=
  { plainColumn with name := .ofString "w", foreignKeys := [parentReference], defaultValue := some numberDefault }

/-- Every declaration of the first two tables names only columns of its table. -/
theorem declared (checked : ∀ position, position = 0 ∨ position = 1 → (input.raw.table position).all
      (fun table => table.shape.allForeignKeys.all fun key => key.columns.all (· < table.shape.columns.length)) = true)
    (target : Nat) (member : target = 0 ∨ target = 1) : input.raw.DeclarationsBelowAt target := by
  intro table found key inside place columns
  have all := checked target member
  rw [found] at all
  simp only [Option.all_some, List.all_eq_true, decide_eq_true_eq] at all
  exact all key inside place columns

/-- The check of {name}`declared` on the input. -/
theorem inputDeclared (position : Nat) (member : position = 0 ∨ position = 1) : (input.raw.table position).all
    (fun table => table.shape.allForeignKeys.all fun key => key.columns.all (· < table.shape.columns.length)) = true := by
  rcases member with rfl | rfl <;> decide +kernel

/-- Rows, declarations and parent selection of the child are as ADD COLUMN requires. -/
theorem wideDeclaredBelow : input.raw.RowsWideAt 1 ∧ input.raw.DeclarationsBelowAt 1 ∧ input.raw.SelectionBelowAt 1 :=
  ⟨Database.rowsWideAt_of_admitted input.valid.admitted 1, declared inputDeclared 1 (.inr rfl),
    Database.selectionBelowAt_of_admitted input.valid.admitted 1⟩

/-- A column without constraints has no new declaration to satisfy. -/
theorem plainCondition : (Resolved.Statement.addColumn 1 plainColumn false).ForeignKeyAtomsCondition Profile.pinned input.raw :=
  ⟨⟨wideDeclaredBelow.1, wideDeclaredBelow.2.1, wideDeclaredBelow.2.2,
    fun _ _ _ _ _ _ inside => absurd inside (by simp [plainColumn])⟩,
    fun _ inside => absurd inside (by simp [plainColumn])⟩

/-- Both atoms hold after a fresh run of the ADD COLUMN. -/
theorem addRun : (runSql [(.addColumn 1 plainColumn false, [])] input.raw).Holds
    (fun result => result.ParentSchemasCompatible result.catalog.foreignKeyMapping ∧
      result.RowReferencesHold result.catalog.foreignKeyMapping) :=
  runSql_foreignKeyAtomsSelected Profile.pinned _ inputAtoms (single plainCondition)

/-- The run succeeds and appends a cell to each child row. -/
theorem addRuns : Succeeds (fun result => (result.rowsAt 1).map (·.values.length) = [2, 2])
    (runSql [(.addColumn 1 plainColumn false, [])] input.raw) := by decide +kernel

/-- The statement refuses a column that references the parent with the default 99 on a populated
table. The rows of the child are not empty, so the statement needs no condition on its added cell. -/
theorem refusedCondition : (Resolved.Statement.addColumn 1 numberColumn true).ForeignKeyAtomsCondition
    Profile.pinned input.raw := by
  refine ⟨⟨wideDeclaredBelow.1, wideDeclaredBelow.2.1, wideDeclaredBelow.2.2, ?_⟩, ?_⟩
  · intro table value found _ flagged
    change some _ = some table at found
    cases found
    exact absurd (flagged rfl) (by decide +kernel)
  · intro key inside
    change key ∈ [_] at inside
    simp only [List.mem_singleton] at inside
    subst key
    decide +kernel

/-- Both atoms hold after a fresh run of the refused ADD COLUMN, which fails and keeps the input. -/
theorem refusedRun : (runSql [(.addColumn 1 numberColumn true, [])] input.raw).Holds
    (fun result => result.ParentSchemasCompatible result.catalog.foreignKeyMapping ∧
      result.RowReferencesHold result.catalog.foreignKeyMapping) :=
  runSql_foreignKeyAtomsSelected Profile.pinned _ inputAtoms (single refusedCondition)

/-- The refusal is the error {name}`ExecutionError.referenceColumnDefault` with the input database. -/
theorem refusedFails : (runStatement 0 {} [] (.addColumn 1 numberColumn true) input.raw).effect =
    .error (.referenceColumnDefault, input.raw) := by decide +kernel

/-- Without the refusal, the same column succeeds and breaks the row atom, so the condition on the
added cells is needed. -/
theorem unrefusedBreaksRows : (runStatement 0 {} [] (.addColumn 1 numberColumn false) input.raw).effect.isOk = true ∧
    ¬(effectDatabase (runStatement 0 {} [] (.addColumn 1 numberColumn false) input.raw).effect).RowReferencesHold
      (effectDatabase (runStatement 0 {} [] (.addColumn 1 numberColumn false) input.raw).effect).catalog.foreignKeyMapping := by
  decide +kernel

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

end ForeignKeyDdlRunsFixture

#print axioms ForeignKeyDdlRunsFixture.inputAtoms
#print axioms ForeignKeyDdlRunsFixture.single
#print axioms ForeignKeyDdlRunsFixture.parentReference
#print axioms ForeignKeyDdlRunsFixture.createCondition
#print axioms ForeignKeyDdlRunsFixture.createRun
#print axioms ForeignKeyDdlRunsFixture.createRuns
#print axioms ForeignKeyDdlRunsFixture.forwardRowsRun
#print axioms ForeignKeyDdlRunsFixture.forwardIsOutsideAtoms
#print axioms ForeignKeyDdlRunsFixture.forwardBreaksSchema
#print axioms ForeignKeyDdlRunsFixture.declared
#print axioms ForeignKeyDdlRunsFixture.inputDeclared
#print axioms ForeignKeyDdlRunsFixture.wideDeclaredBelow
#print axioms ForeignKeyDdlRunsFixture.plainCondition
#print axioms ForeignKeyDdlRunsFixture.addRun
#print axioms ForeignKeyDdlRunsFixture.addRuns
#print axioms ForeignKeyDdlRunsFixture.refusedCondition
#print axioms ForeignKeyDdlRunsFixture.refusedRun
#print axioms ForeignKeyDdlRunsFixture.refusedFails
#print axioms ForeignKeyDdlRunsFixture.unrefusedBreaksRows
#print axioms ForeignKeyDdlRunsFixture.keptHaveNone
#print axioms ForeignKeyDdlRunsFixture.dropChildCondition
#print axioms ForeignKeyDdlRunsFixture.dropRun
#print axioms ForeignKeyDdlRunsFixture.dropRuns
#print axioms ForeignKeyDdlRunsFixture.dropParentBreaksRows
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
#print axioms Belay.Sqlite.Model.runScriptFrom_parentSchemasCompatibleSelected
#print axioms Belay.Sqlite.Model.foreignKeyAtomsSelected_statementKeeps
#print axioms Belay.Sqlite.Model.runSqlFrom_foreignKeyAtomsSelected
#print axioms Belay.Sqlite.Model.runSql_foreignKeyAtomsSelected
#print axioms Belay.Sqlite.Model.runScriptFrom_foreignKeyAtomsSelected
