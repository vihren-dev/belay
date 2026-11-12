import Belay.Sqlite.Model.Schema.Ddl.KeysUniqueDrop
import Belay.Sqlite.Model.Schema.Rows.RowLocalAtoms

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every atom, database and positions: if every table of the database has the atom, every
table of the database after {name}`Database.drop` has it. Proof sketch: a table after the drop is
a table of the database ({name}`Database.table_drop_cases`). -/
theorem Database.EachTable.drop {atom : Table → Prop} {database : Database} (every : database.EachTable atom)
    (positions : List Nat) : (database.drop positions).EachTable atom := by
  intro position table present
  obtain ⟨old, _, _, found⟩ := Database.table_drop_cases present
  exact every old table found

/-- For every atom, clock value, counters, parameter list, CREATE TABLE and database: if the atom is a
{name}`RowLocalAtom` and every table of the database has it, the effect of {name}`runStatement`
satisfies "every table has the atom" ({name}`Effect.Satisfies`): the database of a success and that
of an error with {name}`ExecutionError.constraintFail` have it, and any other error requires
nothing. The new table has no rows. Proof
sketch: {name}`Database.EachTable.appendEmpty`; every error keeps the database. -/
theorem runStatement_createTable_rowLocal {atom : Table → Prop} (rowLocal : RowLocalAtom atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier) (shape : CatalogTable) {database : Database}
    (every : database.EachTable atom) :
    (runStatement clock counters parameters (.createTable target name shape) database).effect.Satisfies
      fun after => after.EachTable atom := by
  simp only [runStatement, step]
  split
  · rename_i fits
    simp only [Bool.and_eq_true, beq_iff_eq] at fits
    exact Effect.satisfies_of_effectDatabase (every.appendEmpty rowLocal.toTableAtom fits.2 _)
  · exact Effect.satisfies_of_database every rfl

/-- For every atom, clock value, counters, parameter list, CREATE VIEW and database: if the atom is a
{name}`RowLocalAtom` and every table of the database has it, the effect of {name}`runStatement`
satisfies "every table has the atom" ({name}`Effect.Satisfies`): the database of a success and that
of an error with {name}`ExecutionError.constraintFail` have it, and any other error requires
nothing. A view has no rows. Proof sketch:
{name}`Database.EachTable.appendEmpty`; every error keeps the database. -/
theorem runStatement_createView_rowLocal {atom : Table → Prop} (rowLocal : RowLocalAtom atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier) (view : CatalogView) {database : Database}
    (every : database.EachTable atom) :
    (runStatement clock counters parameters (.createView target name view) database).effect.Satisfies
      fun after => after.EachTable atom := by
  simp only [runStatement, step]
  split
  · rename_i fits
    simp only [Bool.and_eq_true, beq_iff_eq] at fits
    exact Effect.satisfies_of_effectDatabase (every.appendEmpty rowLocal.toTableAtom fits.2 _)
  · exact Effect.satisfies_of_database every rfl

/-- For every atom, clock value, counters, parameter list, CREATE TRIGGER and database: if the atom is a
{name}`RowLocalAtom` and every table of the database has it, the effect of {name}`runStatement`
satisfies "every table has the atom" ({name}`Effect.Satisfies`): the database of a success and that
of an error with {name}`ExecutionError.constraintFail` have it, and any other error requires
nothing. A trigger has no rows. Proof sketch:
{name}`Database.EachTable.appendEmpty`; every error keeps the database. -/
theorem runStatement_createTrigger_rowLocal {atom : Table → Prop} (rowLocal : RowLocalAtom atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier) (trigger : CatalogTrigger) {database : Database}
    (every : database.EachTable atom) :
    (runStatement clock counters parameters (.createTrigger target name trigger) database).effect.Satisfies
      fun after => after.EachTable atom := by
  simp only [runStatement, step]
  split
  · rename_i fits
    simp only [Bool.and_eq_true, beq_iff_eq] at fits
    exact Effect.satisfies_of_effectDatabase (every.appendEmpty rowLocal.toTableAtom fits.2 _)
  · exact Effect.satisfies_of_database every rfl

/-- For every atom, clock value, counters, parameter list, CREATE INDEX and database: if the atom is a
{name}`RowLocalAtom` and every table of the database has it, the effect of {name}`runStatement`
satisfies "every table has the atom" ({name}`Effect.Satisfies`): the database of a success and that
of an error with {name}`ExecutionError.constraintFail` have it, and any other error requires
nothing. An index has no rows and changes no table. Proof sketch:
{name}`Database.EachTable.appendEmpty`; every error keeps the database. -/
theorem runStatement_createIndex_rowLocal {atom : Table → Prop} (rowLocal : RowLocalAtom atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (target : Nat) (name : Identifier) (index : CatalogIndex) {database : Database}
    (every : database.EachTable atom) :
    (runStatement clock counters parameters (.createIndex target name index) database).effect.Satisfies
      fun after => after.EachTable atom := by
  simp only [runStatement, step]
  split
  · rename_i fits
    simp only [Bool.and_eq_true, beq_iff_eq] at fits
    split
    · exact Effect.satisfies_of_database every rfl
    · split
      · exact Effect.satisfies_of_database every rfl
      · exact Effect.satisfies_of_effectDatabase (every.appendEmpty rowLocal.toTableAtom fits.2 _)
  · exact Effect.satisfies_of_database every rfl

end Belay.Sqlite.Model
