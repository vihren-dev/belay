import Belay.Sqlite.Model.Programs.Scripts.StatementStep
import Belay.Sqlite.Model.Schema.Ddl.KeysUniqueCreate

set_option doc.verso true

/-! The theorems of the atom "keys unique" (ADR 0022, D3, slice 2) for CREATE TABLE, CREATE
INDEX, CREATE VIEW and CREATE TRIGGER. Each appends one object to the catalog and an empty row list, so a
kept table keeps its rows, and the only new unique key of a kept table is the key of a new unique
index on it, which CREATE INDEX checks against the rows. -/

namespace Belay.Sqlite.Model

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
