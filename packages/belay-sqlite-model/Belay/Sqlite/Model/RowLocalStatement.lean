import Belay.Sqlite.Model.AdmittedTableAtomStatement
import Belay.Sqlite.Model.RowLocalUpsert

set_option doc.verso true

/-! The statement theorem of the atoms "not null", "types fit" and "checks hold" (ADR 0022, D3,
slice 3), stated for every {lit}`RowLocalAtom` at once, for every constructor of
{lit}`Resolved.Statement`: the writes without rules are the theorems of part 1, the writes with
foreign key rules and trigger programs are writes of the row engine ({lit}`RowEngineWrites`), and
ADD COLUMN takes the condition of the atom as a hypothesis. {lit}`ValidAtomsStatement` gives the
three instances. -/

namespace Belay.Sqlite.Model

/-- The statement theorem for every atom. For every atom, clock value, counters, parameter list, resolved
statement and database: if the atom is a {name}`RowLocalAtom`, every table of the database has it,
and, when the statement is ADD COLUMN at a target with a column, the table at the target with the
column and every added cell ({name}`AddedCell`) appended has the atom, the effect of
{name}`runStatement` satisfies "every table has the atom" ({name}`Effect.Satisfies`): the database
of a success and that of an error with {name}`ExecutionError.constraintFail` have it, and any other
error requires nothing. It has no condition on the connection, the support check or the clock.
Proof sketch: apply {name}`runStatement_tableAtom` to the inherited table frame evidence and
{name}`RowLocalAtom.facts`. The independent ADD COLUMN premise and the plain INSERT, UPDATE,
upsert and INSERT-query facts supply its remaining hypotheses. The shared theorem handles
all constructors, including rename, clean column drops and rule-bearing writes.
The ADD COLUMN premise covers either value of the refusal flag. -/
theorem runStatement_rowLocal {atom : Table → Prop} (rowLocal : RowLocalAtom atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (statement : Resolved.Statement) {database : Database}
    (every : database.EachTable atom)
    (appended : ∀ target column refuses, statement = .addColumn target column refuses → ∀ table value,
      database.table target = some table → AddedCell table column value →
        atom (table.appendColumns [(column, value)])) :
    (runStatement clock counters parameters statement database).effect.Satisfies fun after => after.EachTable atom := by
  apply runStatement_tableAtom rowLocal.toTableAtom rowLocal.facts.laws
    clock counters parameters statement every
  · intro target column refuses table value same found added
    exact appended target column refuses same table value found added
  · rintro ⟨target, cells, query, clauses, returning, algorithm, subqueries, rfl⟩
    exact runStatement_insertSelect_none_satisfies clock counters parameters target cells query clauses
      returning algorithm subqueries every fun literals => Effect.satisfies_of_effectDatabase
        (runStatement_upsert_rowLocal rowLocal clock counters parameters target literals clauses returning
          algorithm subqueries every)
  · rintro (⟨target, rows, returning, subqueries, rfl⟩ |
      ⟨target, assignments, filter, returning, subqueries, rfl⟩ |
      ⟨target, rows, clauses, returning, algorithm, subqueries, rfl⟩)
    · exact runStatement_insert_rowLocal rowLocal clock counters parameters
        target rows returning subqueries every
    · exact runStatement_update_rowLocal rowLocal clock counters parameters
        target assignments filter returning subqueries every
    · exact Effect.satisfies_of_effectDatabase
        (runStatement_upsert_rowLocal rowLocal clock counters parameters
          target rows clauses returning algorithm subqueries every)

end Belay.Sqlite.Model
