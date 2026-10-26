import Belay
import Belay.Sqlite.Model.ForeignKeyAddColumn
import Belay.Sqlite.Model.ForeignKeyAddColumnValid

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! ADD COLUMN keeps both foreign-key atoms when the new cells are NULL, or the table is empty, and
the premises on the target hold. A non-NULL default on a populated table needs the refusal, which
the resolver sets while foreign keys are enforced. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyAddColumnFixture

/-- Two matching child rows make preservation nonvacuous. -/
def input : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k));
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1),(1);"

/-- The same schema with no child row. -/
def emptyChild : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p(k));
  INSERT INTO p VALUES(1);"

/-- A column without constraints. -/
def plainColumn : CatalogColumn := {name := .ofString "y", declaredType := none}

/-- The declaration that a new column at position one of the child table adds. -/
def reference : ForeignKey :=
  {table := .ofString "p", columns := [1], referenced := [.ofString "k"], onDelete := .noAction, onUpdate := .noAction}

/-- A column that references the parent and has no default. -/
def nullReference : CatalogColumn := {plainColumn with name := .ofString "z", foreignKeys := [reference]}

/-- The default 99, for which the parent has no row. -/
def numberDefault : ColumnDefault :=
  { form := .literal (.value (.integer 99)) (.integer 99), sourceText := "99" }

/-- A column that references the parent and has the default 99. -/
def numberReference : CatalogColumn :=
  { nullReference with name := .ofString "w", defaultValue := some numberDefault }

/-- Both atoms hold on the inputs. -/
theorem inputAtoms : input.raw.ParentSchemasCompatible input.raw.catalog.foreignKeyMapping ∧
    input.raw.RowReferencesHold input.raw.catalog.foreignKeyMapping := by decide +kernel

/-- Both atoms hold on the input without child rows. -/
theorem emptyAtoms : emptyChild.raw.ParentSchemasCompatible emptyChild.raw.catalog.foreignKeyMapping ∧
    emptyChild.raw.RowReferencesHold emptyChild.raw.catalog.foreignKeyMapping := by decide +kernel

/-- Every declaration of the first two tables names only columns of its table. -/
theorem declared (database : Belay.Sqlite.Database)
    (checked : ∀ position, position = 0 ∨ position = 1 → (database.raw.table position).all
      (fun table => table.shape.allForeignKeys.all fun key => key.columns.all (· < table.shape.columns.length)) = true)
    (target : Nat) (member : target = 0 ∨ target = 1) : database.raw.DeclarationsBelowAt target := by
  intro table found key inside place columns
  have all := checked target member
  rw [found] at all
  simp only [Option.all_some, List.all_eq_true, decide_eq_true_eq] at all
  exact all key inside place columns

/-- The check of {name}`declared` on the input. -/
theorem inputDeclared (position : Nat) (_ : position = 0 ∨ position = 1) : (input.raw.table position).all
    (fun table => table.shape.allForeignKeys.all fun key => key.columns.all (· < table.shape.columns.length)) = true := by
  rcases ‹position = 0 ∨ position = 1› with rfl | rfl <;> decide +kernel

/-- A column without constraints keeps both atoms in the child table and in the parent table. -/
theorem plainPreserved (target : Nat) (member : target = 0 ∨ target = 1) :
    (runStatement 0 {} [] (.addColumn target plainColumn false) input.raw).effect.Satisfies
      (fun result => result.ParentSchemasCompatible result.catalog.foreignKeyMapping ∧
        result.RowReferencesHold result.catalog.foreignKeyMapping) :=
  runStatement_addColumn_foreignKeyAtoms 0 {} [] target plainColumn false inputAtoms
    (Database.rowsWideAt_of_admitted input.valid.admitted target)
    (declared input inputDeclared target member)
    (Database.selectionBelowAt_of_admitted input.valid.admitted target)
    (fun _ inside => absurd inside (by simp [plainColumn]))
    (fun _ _ _ _ _ _ inside => absurd inside (by simp [plainColumn]))

/-- A new reference without a default stores NULL in each old row, which no parent row must match. -/
theorem nullReferencePreserved : (runStatement 0 {} [] (.addColumn 1 nullReference false) input.raw).effect.Satisfies
    (fun result => result.ParentSchemasCompatible result.catalog.foreignKeyMapping ∧
      result.RowReferencesHold result.catalog.foreignKeyMapping) := by
  apply runStatement_addColumn_foreignKeyAtoms 0 {} [] 1 nullReference false inputAtoms
    (Database.rowsWideAt_of_admitted input.valid.admitted 1)
    (declared input inputDeclared 1 (.inr rfl))
    (Database.selectionBelowAt_of_admitted input.valid.admitted 1)
  · intro key inside
    simp only [nullReference, plainColumn, List.mem_singleton] at inside
    subst key
    decide +kernel
  · intro table value found added _ key inside row inRows
    simp only [nullReference, plainColumn, List.mem_singleton] at inside
    subst key
    rcases added with empty | ⟨read, _, _⟩
    · rw [empty] at inRows
      cases inRows
    · have isNull : value = .null := by
        have stored : readDefaultValue nullReference = .ok Value.null := rfl
        exact Except.ok.inj (read.symm.trans stored)
      subst value
      have all : (input.raw.table 1).all (fun table => table.rows.all fun row =>
          ((input.raw.catalog.addColumn 1 nullReference).foreignKeyMapping.link 1 reference).satisfied
            (input.raw.addColumn 1 nullReference .null)
            (row.appendValues [Value.store nullReference.affinity .null])) = true := by decide +kernel
      rw [found] at all
      simp only [Option.all_some, List.all_eq_true] at all
      exact all row inRows

/-- With a default 99 and no parent row 99, the new cells break the row atom when the statement
does not refuse. The parent schema stays compatible. -/
theorem numberNeedsRefusal :
    (runStatement 0 {} [] (.addColumn 1 numberReference false) input.raw).effect.isOk = true ∧
    ¬(effectDatabase (runStatement 0 {} [] (.addColumn 1 numberReference false) input.raw).effect).RowReferencesHold
      (effectDatabase (runStatement 0 {} [] (.addColumn 1 numberReference false) input.raw).effect).catalog.foreignKeyMapping ∧
    (effectDatabase (runStatement 0 {} [] (.addColumn 1 numberReference false) input.raw).effect).ParentSchemasCompatible
      (effectDatabase (runStatement 0 {} [] (.addColumn 1 numberReference false) input.raw).effect).catalog.foreignKeyMapping := by
  decide +kernel

/-- The refusing statement stops at the first check and returns the input database. -/
theorem numberRefused : (runStatement 0 {} [] (.addColumn 1 numberReference true) input.raw).effect =
    .error (.referenceColumnDefault, input.raw) := by decide +kernel

/-- On a table without rows, the refusing statement succeeds and keeps both atoms: the new
declaration has no row to satisfy. -/
theorem emptyAccepted : (runStatement 0 {} [] (.addColumn 1 numberReference true) emptyChild.raw).effect.Satisfies
    (fun result => result.ParentSchemasCompatible result.catalog.foreignKeyMapping ∧
      result.RowReferencesHold result.catalog.foreignKeyMapping) := by
  apply runStatement_addColumn_foreignKeyAtoms 0 {} [] 1 numberReference true emptyAtoms
    (Database.rowsWideAt_of_admitted emptyChild.valid.admitted 1)
    (declared emptyChild (by intro position member; rcases member with rfl | rfl <;> decide +kernel) 1 (.inr rfl))
    (Database.selectionBelowAt_of_admitted emptyChild.valid.admitted 1)
  · intro key inside
    simp only [numberReference, nullReference, plainColumn, List.mem_singleton] at inside
    subst key
    decide +kernel
  · intro table value found added flagged key inside row inRows
    rw [flagged rfl] at inRows
    cases inRows

/-- The statement on the empty table succeeds. -/
theorem emptySucceeds : (runStatement 0 {} [] (.addColumn 1 numberReference true) emptyChild.raw).effect.isOk = true := by
  decide +kernel

end ForeignKeyAddColumnFixture

#print axioms ForeignKeyAddColumnFixture.inputAtoms
#print axioms ForeignKeyAddColumnFixture.emptyAtoms
#print axioms ForeignKeyAddColumnFixture.declared
#print axioms ForeignKeyAddColumnFixture.inputDeclared
#print axioms ForeignKeyAddColumnFixture.plainPreserved
#print axioms ForeignKeyAddColumnFixture.nullReferencePreserved
#print axioms ForeignKeyAddColumnFixture.numberNeedsRefusal
#print axioms ForeignKeyAddColumnFixture.numberRefused
#print axioms ForeignKeyAddColumnFixture.emptyAccepted
#print axioms ForeignKeyAddColumnFixture.emptySucceeds
#print axioms Belay.Sqlite.Model.findPosition_set_same
#print axioms Belay.Sqlite.Model.Catalog.findTable_addColumn
#print axioms Belay.Sqlite.Model.Catalog.filterMap_addColumn
#print axioms Belay.Sqlite.Model.Catalog.parentIndexes_addColumn
#print axioms Belay.Sqlite.Model.getD_append_below
#print axioms Belay.Sqlite.Model.childValues_append
#print axioms Belay.Sqlite.Model.ForeignKeyLink.hasNull_append
#print axioms Belay.Sqlite.Model.ForeignKeyLink.satisfied_append
#print axioms Belay.Sqlite.Model.indexHolds_appendColumn
#print axioms Belay.Sqlite.Model.parentFound_appendColumn
#print axioms Belay.Sqlite.Model.ForeignKeyLink.satisfied_addColumn
#print axioms Belay.Sqlite.Model.Catalog.parentIndexes_appendColumn
#print axioms Belay.Sqlite.Model.mapM_option_congr
#print axioms Belay.Sqlite.Model.findSome?_option_congr
#print axioms Belay.Sqlite.Model.matchIndex_appendColumn
#print axioms Belay.Sqlite.Model.Catalog.parentKey_appendColumn
#print axioms Belay.Sqlite.Model.Catalog.parentLink_addColumn
#print axioms Belay.Sqlite.Model.mapM_option_mem
#print axioms Belay.Sqlite.Model.matchIndex_pairs
#print axioms Belay.Sqlite.Model.Catalog.parentKey_pairs
#print axioms Belay.Sqlite.Model.Database.AddColumnReads.of_selected
#print axioms Belay.Sqlite.Model.Catalog.Valid.selectionBelow
#print axioms Belay.Sqlite.Model.Database.selectionBelowAt_of_admitted
#print axioms Belay.Sqlite.Model.CatalogTable.mem_allForeignKeys_appendColumn
#print axioms Belay.Sqlite.Model.Database.RowReferencesHold.addColumn
#print axioms Belay.Sqlite.Model.Database.ParentSchemasCompatible.addColumn
#print axioms Belay.Sqlite.Model.step_addColumn_refused_populated
#print axioms Belay.Sqlite.Model.runStatement_addColumn_cases
#print axioms Belay.Sqlite.Model.runStatement_addColumn_rowReferences
#print axioms Belay.Sqlite.Model.runStatement_addColumn_parentSchemasCompatible
#print axioms Belay.Sqlite.Model.runStatement_addColumn_foreignKeyAtoms
