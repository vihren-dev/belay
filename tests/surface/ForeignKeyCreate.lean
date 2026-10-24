import Belay
import Belay.Sqlite.Model.ForeignKeyCreate

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! CREATE preserves old matching rows and schema selections. New declarations need
compatible parents even when empty; the row atom remains independent of that condition. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyCreateFixture

/-- Two matching child rows make preservation nonvacuous and permit a failing unique index. -/
def input : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k));
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1),(1);"

/-- Reuse the supported child declaration for a new empty child table. -/
def child : CatalogTable := (input.raw.catalog.tableAt 1).getD {columns := []}

/-- One supported object for each CREATE family. -/
def objects : List CatalogObject :=
  [{name := .ofString "d", entry := .table child},
   {name := .ofString "p_key", entry := .index {table := 0, keys := [{term := .column 0}], unique := true}},
   {name := .ofString "cleanup", entry := .trigger
     {table := .ofString "p", time := .after, event := .insert, body := [.delete (.ofString "c") none]}}]

/-- The raw CREATE statement names the current catalog end and the supplied object. -/
def create (object : CatalogObject) : Resolved.Statement :=
  match object.entry with
  | .table shape => .createTable input.raw.catalog.length object.name shape
  | .index index => .createIndex input.raw.catalog.length object.name index
  | .trigger trigger => .createTrigger input.raw.catalog.length object.name trigger

/-- The test constructor exposes the real object that the statement creates. -/
theorem creates (object : CatalogObject) : (create object).CreatesObject object := by
  cases object with
  | mk name entry => cases entry <;> rfl

/-- All old declarations already have compatible parent choices and matching rows. -/
theorem inputAtoms : input.raw.ParentSchemasCompatible input.raw.catalog.foreignKeyMapping ∧
    input.raw.RowReferencesHold input.raw.catalog.foreignKeyMapping := by decide +kernel

/-- Both atoms survive each CREATE by the common public theorem and its new-declaration condition. -/
theorem creationsPreserve (object : CatalogObject) (member : object ∈ objects) :
    (runStatement 0 {} [] (create object) input.raw).effect.Satisfies
      (fun result => result.ParentSchemasCompatible result.catalog.foreignKeyMapping ∧
        result.RowReferencesHold result.catalog.foreignKeyMapping) := by
  apply runStatement_create_foreignKeyAtoms 0 {} [] (create object) object (creates object) inputAtoms
  intro shape entry key declared
  simp only [objects, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · cases entry
    change key ∈ [_] at declared
    simp only [List.mem_singleton] at declared
    subst key
    decide +kernel
  · cases entry
  · cases entry

/-- All three CREATE statements succeed and retain both original child rows. -/
theorem creationsSucceed : objects.all (fun object =>
    let result := runStatement 0 {} [] (create object) input.raw
    result.effect.isOk && ((effectDatabase result.effect).rowsAt 1).length == 2 &&
      (effectDatabase result.effect).catalog.length == 3) = true := by decide +kernel

/-- A new empty table refers to an absent parent. Its row fact is still vacuous. -/
def forward : CatalogObject :=
  {name := .ofString "forward", entry := .table {child with columns := child.columns.map fun column =>
    {column with foreignKeys := column.foreignKeys.map fun key => {key with table := .ofString "missing"}}}}

/-- The flexible row-only CREATE law does not require compatibility of the new declaration. -/
theorem forwardRowsPreserved : (runStatement 0 {} [] (create forward) input.raw).effect.Satisfies
    (fun result => result.RowReferencesHold result.catalog.foreignKeyMapping) := by
  apply runStatement_create_rowReferences Catalog.foreignKeyMapping 0 {} [] (create forward) forward
    (creates forward) inputAtoms.2
  exact inputAtoms.1.selection_append [forward]

/-- CREATE with a forward reference succeeds, keeps row truth and breaks schema compatibility. -/
theorem forwardNeedsSchemaPremise :
    (runStatement 0 {} [] (create forward) input.raw).effect.isOk = true ∧
    (effectDatabase (runStatement 0 {} [] (create forward) input.raw).effect).RowReferencesHold
      (effectDatabase (runStatement 0 {} [] (create forward) input.raw).effect).catalog.foreignKeyMapping ∧
    ¬(effectDatabase (runStatement 0 {} [] (create forward) input.raw).effect).ParentSchemasCompatible
      (effectDatabase (runStatement 0 {} [] (create forward) input.raw).effect).catalog.foreignKeyMapping := by decide +kernel

/-- A unique index over the duplicate child values fails and carries the original database. -/
theorem duplicateIndexRejected :
    (runStatement 0 {} [] (.createIndex 2 (.ofString "c_unique")
      {table := 1, keys := [{term := .column 0}], unique := true}) input.raw).effect =
      .error (.constraintViolation, input.raw) := by rfl

end ForeignKeyCreateFixture

#print axioms ForeignKeyCreateFixture.creates
#print axioms ForeignKeyCreateFixture.inputAtoms
#print axioms ForeignKeyCreateFixture.creationsPreserve
#print axioms ForeignKeyCreateFixture.creationsSucceed
#print axioms ForeignKeyCreateFixture.forwardRowsPreserved
#print axioms ForeignKeyCreateFixture.forwardNeedsSchemaPremise
#print axioms ForeignKeyCreateFixture.duplicateIndexRejected
#print axioms Belay.Sqlite.Model.Database.rowsAt_appendEmpty
#print axioms Belay.Sqlite.Model.ForeignKeyLink.satisfied_appendEmpty
#print axioms Belay.Sqlite.Model.Database.RowReferencesHold.appendEmpty
#print axioms Belay.Sqlite.Model.Catalog.tableAt_append_cases
#print axioms Belay.Sqlite.Model.Database.ParentSchemasCompatible.appendEmpty
#print axioms Belay.Sqlite.Model.Catalog.parentKey_append_of_some
#print axioms Belay.Sqlite.Model.Catalog.parentLink_append_of_located
#print axioms Belay.Sqlite.Model.Database.ParentSchemasCompatible.selection_append
#print axioms Belay.Sqlite.Model.runStatement_create_frame
#print axioms Belay.Sqlite.Model.runStatement_create_rowReferences
#print axioms Belay.Sqlite.Model.runStatement_create_parentSchemasCompatible
#print axioms Belay.Sqlite.Model.runStatement_create_foreignKeyAtoms
