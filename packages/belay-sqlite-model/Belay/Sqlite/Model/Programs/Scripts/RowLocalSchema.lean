import Belay.Sqlite.Model.Programs.Scripts.KeysUniqueDrop
import Belay.Sqlite.Model.Schema.Rows.RowLocalSchema

set_option doc.verso true

/-! The theorems of the atoms "not null", "types fit" and "checks hold" (ADR 0022, D3, slice 3),
stated for every {lit}`RowLocalAtom`, for CREATE TABLE, CREATE INDEX, CREATE TRIGGER, CREATE VIEW
and DROP without the row engine. The four CREATE forms append one object and an empty row list, so every kept
table is a table of the database or has no rows. A drop keeps its tables whole, with their rows
and entries, so it keeps every such atom for every database, without a condition: the atoms read
no index and no position. {lit}`ValidAtomsStatement` states them for each atom. -/

namespace Belay.Sqlite.Model

/-- For every atom, clock value, counters, parameter list, DROP without foreign key rules and trigger
programs ({lean}`(none : Option Resolved.WriteRules)`) and database: if every table of the database
has the atom, the effect of {name}`runStatement` satisfies "every table has the atom"
({name}`Effect.Satisfies`): the database of a success and that of an error with
{name}`ExecutionError.constraintFail` have it, and any other error requires nothing. The atom
need not be a {name}`RowLocalAtom`, and DROP has no condition. Proof sketch: the effect is the
database after {name}`Database.drop` ({name}`Database.EachTable.drop`). -/
theorem runStatement_drop_rowLocal {atom : Table → Prop} (clock : Int) (counters : Counters) (parameters : List Value)
    (positions : List Nat) {database : Database} (every : database.EachTable atom) :
    (runStatement clock counters parameters (.drop positions none) database).effect.Satisfies fun after => after.EachTable atom := by
  simp only [runStatement, Option.map_none, StatementRun.withKeys, step]
  exact Effect.satisfies_of_effectDatabase (every.drop positions)

end Belay.Sqlite.Model
