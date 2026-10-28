import Belay.Sqlite.Model.DatabaseConstraintChecks
import Belay.Sqlite.Model.KeysUniqueFrame
import Belay.Sqlite.Model.TableAtomFrames
import Belay.Sqlite.Model.StatementStep

set_option doc.verso true

/-! The theorems of the atom "keys unique" (ADR 0022, D3, slice 2) for CREATE TABLE, CREATE
INDEX, CREATE VIEW and CREATE TRIGGER. Each appends one object to the catalog and an empty row list, so a
kept table keeps its rows, and the only new unique key of a kept table is the key of a new unique
index on it, which CREATE INDEX checks against the rows. -/

namespace Belay.Sqlite.Model

/-- For every catalog, object, position, table entry and key: if the key is a unique key of the
position in the catalog with the object appended ({name}`Catalog.uniqueKeys`), it is a unique
key of the position in the catalog, or the object is a unique index on the position and the key
is its key ({name}`CatalogIndex.uniqueKey`). Proof sketch: the keys of the appended catalog are
the old keys followed by the key of the object, which is present only for a unique index on the
position. -/
theorem Catalog.mem_uniqueKeys_append {catalog : Catalog} {object : CatalogObject} {position : Nat}
    {shape : CatalogTable} {key : UniqueKey} (member : key ∈ (catalog ++ [object]).uniqueKeys position shape) :
    key ∈ catalog.uniqueKeys position shape ∨ ∃ index, object.entry = .index index ∧ index.table = position ∧
      index.unique = true ∧ key = index.uniqueKey := by
  unfold Catalog.uniqueKeys at member ⊢
  rw [List.filterMap_append, ← List.append_assoc, List.mem_append] at member
  rcases member with old | new
  · exact .inl old
  · refine .inr ?_
    simp only [List.filterMap_cons, List.filterMap_nil] at new
    cases entry : object.entry with
    | table _ | view _ | trigger _ => simp [entry] at new
    | index index =>
      simp only [entry] at new
      by_cases on : index.table = position ∧ index.unique = true
      · simp only [on, beq_self_eq_true, Bool.and_self, ↓reduceIte, List.mem_singleton] at new
        exact ⟨index, rfl, on.1, on.2, new⟩
      · have off : (index.table == position && index.unique) = false := by
          simpa [Bool.and_eq_true, beq_iff_eq] using on
        simp [off] at new

/-- For every database whose row lists match its catalog and object: if the database satisfies
{name}`Database.KeysUnique`, and when the object is a unique index on a table its rows have no
two rows that conflict on its key, then the database with the object and an empty row list
appended satisfies {name}`Database.KeysUnique`. Proof sketch: a table with rows is a table of
the database ({name}`Database.table_append_cases`), and each of its keys is an old key or the
key of the new index ({name}`Catalog.mem_uniqueKeys_append`). -/
theorem Database.KeysUnique.append {database : Database} (unique : database.KeysUnique)
    (aligned : database.rows.length = database.catalog.length) (object : CatalogObject)
    (newKey : ∀ index table, object.entry = .index index → index.unique = true → database.table index.table = some table →
      table.rows.Pairwise fun first second => LiteralData.keyEqual index.uniqueKey first second = false) :
    ({ catalog := database.catalog ++ [object], rows := database.rows ++ [[]] } : Database).KeysUnique := by
  intro position table present
  rcases Database.table_append_cases aligned object present with old | empty
  · intro key member
    rcases Catalog.mem_uniqueKeys_append member with kept | ⟨index, entry, on, isUnique, same⟩
    · exact unique position table old key kept
    · subst same on
      exact newKey index table entry isUnique old
  · intro key _
    rw [empty]
    exact List.Pairwise.nil

/-- For every clock value, counters, parameter list, CREATE TABLE and database: if the database satisfies
{name}`Database.KeysUnique`, the effect of {name}`runStatement` satisfies
{name}`Effect.Satisfies` for {name}`Database.KeysUnique`. The new table has no rows. Proof sketch:
{name}`Database.KeysUnique.append` of a table entry, which is no index. -/
theorem runStatement_createTable_keysUnique (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier)
    (shape : CatalogTable) {database : Database} (unique : database.KeysUnique) :
    (runStatement clock counters parameters (.createTable target name shape) database).effect.Satisfies Database.KeysUnique := by
  simp only [runStatement, step]
  split
  · rename_i fits
    simp only [Bool.and_eq_true, beq_iff_eq] at fits
    exact Effect.satisfies_of_effectDatabase (unique.append fits.2 _ fun _ _ entry => by cases entry)
  · exact Effect.satisfies_of_database unique rfl

/-- For every clock value, counters, parameter list, CREATE VIEW and database: if the database
satisfies {name}`Database.KeysUnique`, the effect of {name}`runStatement` satisfies
{name}`Effect.Satisfies` for {name}`Database.KeysUnique`. That is: if the effect succeeds, or fails with
{name}`ExecutionError.constraintFail`, its database has unique keys; an error with another reason
requires nothing. A view has no stored keys. Proof sketch:
{name}`Database.KeysUnique.append` of a view entry, which is no index. -/
theorem runStatement_createView_keysUnique (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier)
    (view : CatalogView) {database : Database} (unique : database.KeysUnique) :
    (runStatement clock counters parameters (.createView target name view) database).effect.Satisfies Database.KeysUnique := by
  simp only [runStatement, step]
  split
  · rename_i fits
    simp only [Bool.and_eq_true, beq_iff_eq] at fits
    exact Effect.satisfies_of_effectDatabase (unique.append fits.2 _ fun _ _ entry => by cases entry)
  · exact Effect.satisfies_of_database unique rfl

/-- For every clock value, counters, parameter list, CREATE TRIGGER and database: if the database
satisfies {name}`Database.KeysUnique`, the effect of {name}`runStatement` satisfies
{name}`Effect.Satisfies` for {name}`Database.KeysUnique`. A trigger has no key. Proof sketch:
{name}`Database.KeysUnique.append` of a trigger entry, which is no index. -/
theorem runStatement_createTrigger_keysUnique (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier)
    (trigger : CatalogTrigger) {database : Database} (unique : database.KeysUnique) :
    (runStatement clock counters parameters (.createTrigger target name trigger) database).effect.Satisfies Database.KeysUnique := by
  simp only [runStatement, step]
  split
  · rename_i fits
    simp only [Bool.and_eq_true, beq_iff_eq] at fits
    exact Effect.satisfies_of_effectDatabase (unique.append fits.2 _ fun _ _ entry => by cases entry)
  · exact Effect.satisfies_of_database unique rfl

/-- For every clock value, counters, parameter list, CREATE INDEX and database: if the database satisfies
{name}`Database.KeysUnique`, the effect of {name}`runStatement` satisfies
{name}`Effect.Satisfies` for {name}`Database.KeysUnique`. A unique index is created only when no two rows of its table conflict
on its key ({name}`LiteralData.uniqueRows`). Proof sketch: {name}`Database.KeysUnique.append`,
with {name}`uniqueRows_iff` for the key of the new index. -/
theorem runStatement_createIndex_keysUnique (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier)
    (index : CatalogIndex) {database : Database} (unique : database.KeysUnique) :
    (runStatement clock counters parameters (.createIndex target name index) database).effect.Satisfies Database.KeysUnique := by
  simp only [runStatement, step]
  split
  · rename_i fits
    simp only [Bool.and_eq_true, beq_iff_eq] at fits
    split
    · exact Effect.satisfies_of_database unique rfl
    · rename_i table found
      split
      · exact Effect.satisfies_of_database unique rfl
      · rename_i passes
        refine Effect.satisfies_of_effectDatabase (unique.append fits.2 _ fun same other entry isUnique present => ?_)
        cases entry
        rw [found, Option.some.injEq] at present
        subst present
        simp only [isUnique, Bool.true_and, Bool.not_eq_true'] at passes
        exact (uniqueRows_iff _ _).mp (by simpa using passes)
  · exact Effect.satisfies_of_database unique rfl

end Belay.Sqlite.Model
