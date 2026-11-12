import Belay.Sqlite.Model.Schema.Rows.TableAtomWrites
import Belay.Sqlite.Model.Schema.Rows.RowLocalAtoms
import Belay.Sqlite.Model.Programs.Scripts.KeysUniqueWrites

set_option doc.verso true

/-! The theorems of the atoms "not null", "types fit" and "checks hold" (ADR 0022, D3, slice 3),
stated for every {lit}`RowLocalAtom`, for plain INSERT, UPDATE and DELETE, the writes without the
row engine (no foreign keys checked and no trigger programs), and for the statements that write no
row: a query, a setting, a prepare error, BEGIN, COMMIT and ROLLBACK. {lit}`ValidAtomsStatement`
states them for each atom. -/

namespace Belay.Sqlite.Model

/-- For every atom, clock value, counters, parameter list, database and statement that writes no row (a
query, a setting, a prepare error, BEGIN, COMMIT or ROLLBACK): if every table of the database has
the atom, the effect of {name}`runStatement` satisfies "every table has the atom"
({name}`Effect.Satisfies`): the database of a success and that of an error with
{name}`ExecutionError.constraintFail` have it, and any other error requires nothing. Proof sketch:
{name}`runStatement_keeps_database`. -/
theorem runStatement_writesNone_rowLocal {atom : Table → Prop} (clock : Int) (counters : Counters) (parameters : List Value)
    {database : Database} (every : database.EachTable atom) (statement : Resolved.Statement)
    (writesNone : (∃ query subqueries, statement = .query query subqueries) ∨ (∃ setting on, statement = .setting setting on) ∨
      (∃ error, statement = .prepareError error) ∨ statement = .begin ∨ statement = .commit ∨ statement = .rollback) :
    (runStatement clock counters parameters statement database).effect.Satisfies fun after => after.EachTable atom :=
  Effect.satisfies_of_database every (runStatement_keeps_database clock counters parameters database statement writesNone)

end Belay.Sqlite.Model
