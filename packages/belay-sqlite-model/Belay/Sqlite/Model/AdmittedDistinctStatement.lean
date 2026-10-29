import Belay.Sqlite.Model.AdmittedEngineLaws
import Belay.Sqlite.Model.AdmittedInsertAtoms
import Belay.Sqlite.Model.AdmittedUpdateAtoms
import Belay.Sqlite.Model.AdmittedUpsertAtoms
import Belay.Sqlite.Model.AdmittedAddColumnLaws
import Belay.Sqlite.Model.AdmittedTableAtomStatement

set_option doc.verso true

/-! The statement theorem of the atom "rowids distinct" (ADR 0022, D3, slice 4). The write of a table
checks {lit}`LiteralData.rowidsDistinct` before it stores the table, so the theorem needs no support check
and no other atom. -/

namespace Belay.Sqlite.Model

/-- For every clock value, counters, parameter list, resolved statement and database: if the database
satisfies "rowids distinct" ({name}`Database.RowidsDistinct`), the effect of {name}`runStatement`
satisfies it ({name}`Effect.Satisfies`): the database of a success and that of an error with
{name}`ExecutionError.constraintFail` have distinct rowids in every table, and any other error requires
nothing. The theorem has no condition on the connection, on the support check ({name}`StatementRun.ready`)
or on other atoms, and it covers every form of {name}`Resolved.Statement`. Proof sketch: apply {name}`runStatement_tableAtom` with
{name}`Table.rowidsDistinctAtom` and {name}`rowidsDistinctFacts`. Appending columns preserves
rowids, and the existing plain-write and INSERT-query facts discharge the other premises -/
theorem runStatement_rowidsDistinct (clock : Int) (counters : Counters) (parameters : List Value)
    (statement : Resolved.Statement) {database : Database} (distinct : database.RowidsDistinct) :
    (runStatement clock counters parameters statement database).effect.Satisfies Database.RowidsDistinct := by
  apply runStatement_tableAtom Table.rowidsDistinctAtom rowidsDistinctFacts.laws
    clock counters parameters statement distinct
  · intro target column refuses table value _ found _
    exact Table.RowidsDistinct.appendColumns (distinct target table found) [(column, value)]
  · rintro ⟨target, cells, query, clauses, returning, algorithm, subqueries, rfl⟩
    exact runStatement_insertSelect_none_satisfies clock counters parameters target cells query clauses
      returning algorithm subqueries distinct fun literals =>
        runStatement_upsert_rowidsDistinct clock counters parameters target literals clauses returning
          algorithm subqueries distinct
  · rintro (⟨target, rows, returning, subqueries, rfl⟩ |
      ⟨target, assignments, filter, returning, subqueries, rfl⟩ |
      ⟨target, rows, clauses, returning, algorithm, subqueries, rfl⟩)
    · exact runStatement_insert_rowidsDistinct clock counters parameters
        target rows returning subqueries distinct
    · exact runStatement_update_rowidsDistinct clock counters parameters
        target assignments filter returning subqueries distinct
    · exact runStatement_upsert_rowidsDistinct clock counters parameters
        target rows clauses returning algorithm subqueries distinct

end Belay.Sqlite.Model
