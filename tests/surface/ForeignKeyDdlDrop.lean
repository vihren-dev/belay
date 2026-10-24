import Belay
import Belay.Sqlite.Model.ForeignKeyDdlDrop

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! Plain DROP transports parent and child identities, retains supplied row truth after
index loss, and imposes no parent-retention condition for a removed child. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyDdlDropFixture

/-- The unrelated first table shifts both the matching parent and child when removed. -/
def input : Belay.Sqlite.Database := db! r"
  CREATE TABLE pad(x); CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k));
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- The only declared foreign key, used to discharge finite catalog premises. -/
def key : ForeignKey :=
  {columns := [0], table := .ofString "p", referenced := [.ofString "k"],
    onDelete := .noAction, onUpdate := .noAction}

/-- Every declared key in this concrete catalog is the one on child position two. -/
theorem declaration (child : Nat) (table : Table) (present : input.raw.table child = some table)
    (declared : candidate ∈ table.shape.allForeignKeys) : child = 2 ∧ candidate = key := by
  have bound := Database.table_lt present
  change child < 3 at bound
  have choices : child = 0 ∨ child = 1 ∨ child = 2 := by omega
  rcases choices with rfl | rfl | rfl
  all_goals change some _ = some table at present
  all_goals cases present
  · change candidate ∈ [] at declared; cases declared
  · change candidate ∈ [] at declared; cases declared
  · have keys : ((input.raw.catalog.tableAt 2).getD {columns := []}).allForeignKeys = [key] := by decide +kernel
    change candidate ∈ ((input.raw.catalog.tableAt 2).getD {columns := []}).allForeignKeys at declared
    rw [keys] at declared
    exact ⟨rfl, List.mem_singleton.mp declared⟩

/-- Parent-schema compatibility and nonempty matching child rows hold initially. -/
theorem inputAtoms : input.raw.ParentSchemasCompatible input.raw.catalog.foreignKeyMapping ∧
    input.raw.RowReferencesHold input.raw.catalog.foreignKeyMapping := by decide +kernel

/-- The schema's parent definition and ordered indexes suffice for selection transport. -/
theorem selection : ∀ child table, input.raw.table child = some table → !([0] : List Nat).contains child →
    ∀ candidate ∈ table.shape.allForeignKeys,
      (input.raw.catalog.drop [0]).parentLink candidate =
        (input.raw.catalog.parentLink candidate).transport (keptBelow [0]) := by
  apply inputAtoms.1.selection_drop [0]
  intro child table present kept candidate declared parent shape found
  obtain ⟨rfl, rfl⟩ := declaration child table present declared
  have lookup : input.raw.catalog.findTable key.table =
      some (1, (input.raw.catalog.tableAt 1).getD {columns := []}) := by decide +kernel
  rw [lookup] at found
  cases found
  exact ⟨by decide, by decide +kernel⟩

/-- The combined public theorem preserves both atoms while parent and child positions move. -/
theorem shiftedAtoms : (runStatement 0 {} [] (.drop [0] none) input.raw).effect.Satisfies
    (fun result => result.ParentSchemasCompatible result.catalog.foreignKeyMapping ∧
      result.RowReferencesHold result.catalog.foreignKeyMapping) := by
  apply runStatement_drop_foreignKeyAtoms 0 {} [] [0] inputAtoms selection
  intro child table present kept candidate declared parent comparison selected
  obtain ⟨rfl, rfl⟩ := declaration child table present declared
  have lookup : input.raw.catalog.parentLink key = .located 1 (.columns [(0, 0)]) := by decide +kernel
  rw [lookup] at selected
  cases selected
  decide

/-- Actual DROP succeeds, moves the selected parent to zero and retains the child at one. -/
theorem shiftedResult : (runStatement 0 {} [] (.drop [0] none) input.raw).effect = .ok (input.raw.drop [0]) ∧
    (input.raw.drop [0]).catalog.parentLink key = .located 0 (.columns [(0, 0)]) ∧
    ((input.raw.drop [0]).rowsAt 1).length = 1 := by decide +kernel

/-- Removing the child together with its parent has no surviving declaration obligation. -/
theorem removedFamily : (runStatement 0 {} [] (.drop [1, 2] none) input.raw).effect.Satisfies
    (fun result => result.ParentSchemasCompatible result.catalog.foreignKeyMapping ∧
      result.RowReferencesHold result.catalog.foreignKeyMapping) := by
  apply runStatement_drop_foreignKeyAtoms 0 {} [] [1, 2] inputAtoms
  all_goals intro child table present kept candidate declared
  all_goals obtain ⟨rfl, rfl⟩ := declaration child table present declared
  all_goals contradiction

/-- The child follows the only supporting parent index in catalog order. -/
def indexed : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k); CREATE UNIQUE INDEX p_key ON p(k); CREATE TABLE c(x REFERENCES p(k));
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- A caller retains the old parent comparison independently of the current catalog choice. -/
def retained (_ : Catalog) : ForeignKeyMapping := ⟨fun _ _ => .located 0 (.columns [(0, 0)])⟩

/-- The flexible row law applies after removing the supporting index and moving the child. -/
theorem indexDropRows : (runStatement 0 {} [] (.drop [1] none) indexed.raw).effect.Satisfies
    (fun result => result.RowReferencesHold (retained result.catalog)) := by
  apply runStatement_drop_rowReferences retained 0 {} [] [1] (by decide +kernel)
  · intro child table present kept candidate declared; rfl
  · intro child table present kept candidate declared parent comparison selected
    cases selected
    decide

/-- Index loss is successful and preserves supplied row truth, but breaks schema compatibility. -/
theorem indexDropNeedsSelection : (runStatement 0 {} [] (.drop [1] none) indexed.raw).effect.isOk = true ∧
    (indexed.raw.drop [1]).RowReferencesHold (retained (indexed.raw.drop [1]).catalog) ∧
    ¬(indexed.raw.drop [1]).ParentSchemasCompatible (retained (indexed.raw.drop [1]).catalog) := by decide +kernel

end ForeignKeyDdlDropFixture

#print axioms ForeignKeyDdlDropFixture.declaration
#print axioms ForeignKeyDdlDropFixture.inputAtoms
#print axioms ForeignKeyDdlDropFixture.selection
#print axioms ForeignKeyDdlDropFixture.shiftedAtoms
#print axioms ForeignKeyDdlDropFixture.shiftedResult
#print axioms ForeignKeyDdlDropFixture.removedFamily
#print axioms ForeignKeyDdlDropFixture.indexDropRows
#print axioms ForeignKeyDdlDropFixture.indexDropNeedsSelection
#print axioms Belay.Sqlite.Model.Catalog.findTable_drop_kept
#print axioms Belay.Sqlite.Model.Database.RowReferencesHold.drop
#print axioms Belay.Sqlite.Model.Catalog.parentLink_drop_of_indexes
#print axioms Belay.Sqlite.Model.Database.ParentSchemasCompatible.drop
#print axioms Belay.Sqlite.Model.Database.ParentSchemasCompatible.selection_drop
#print axioms Belay.Sqlite.Model.runStatement_drop_rowReferences
#print axioms Belay.Sqlite.Model.runStatement_drop_parentSchemasCompatible
#print axioms Belay.Sqlite.Model.runStatement_drop_foreignKeyAtoms
