import Belay.Sqlite.Model.AdmittedEngineLaws
import Belay.Sqlite.Model.AdmittedInsertAtoms
import Belay.Sqlite.Model.AdmittedUpdateAtoms
import Belay.Sqlite.Model.AdmittedUpsertAtoms
import Belay.Sqlite.Model.AdmittedAddColumnLaws
import Belay.Sqlite.Model.AdmittedSchemaStatements
import Belay.Sqlite.Model.RowLocalAddColumnTheorems
import Belay.Sqlite.Model.RowLocalSchema
import Belay.Sqlite.Model.RowLocalWrites
import Belay.Sqlite.Model.InsertSelectLaws
import Belay.Sqlite.Model.StatementRewrite
import Belay.Sqlite.Model.StatementDropColumn
import Belay.Sqlite.Model.DropColumnAdmittedLaws

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
or on other atoms, and it covers every form of {name}`Resolved.Statement`. Proof sketch: a case for each
form; RENAME keeps the rows ({name}`Database.RowidsDistinct.of_outline`), CREATE and DROP keep tables whole or empty ({name}`runStatement_create_tableAtom`), ADD COLUMN
keeps the rowids ({name}`Table.RowidsDistinct.appendColumns`), a write without rules is the theorem of
its form ({name}`runStatement_insert_rowidsDistinct` and its siblings), a write with rules is
a write of the row engine ({name}`rowsKeys_satisfies`, {name}`dropKeys_holds`), and a statement
without writes keeps the database. -/
theorem runStatement_rowidsDistinct (clock : Int) (counters : Counters) (parameters : List Value)
    (statement : Resolved.Statement) {database : Database} (distinct : database.RowidsDistinct) :
    (runStatement clock counters parameters statement database).effect.Satisfies Database.RowidsDistinct := by
  cases statement with
  | createTable target name shape =>
    exact runStatement_create_tableAtom Table.rowidsDistinctAtom clock counters parameters _ distinct
      (.inl ⟨target, name, shape, rfl⟩)
  | createIndex target name index =>
    exact runStatement_create_tableAtom Table.rowidsDistinctAtom clock counters parameters _ distinct
      (.inr (.inl ⟨target, name, index, rfl⟩))
  | createView target name view =>
    exact runStatement_create_tableAtom Table.rowidsDistinctAtom clock counters parameters _ distinct
      (.inr (.inr (.inr ⟨target, name, view, rfl⟩)))
  | createTrigger target name trigger =>
    exact runStatement_create_tableAtom Table.rowidsDistinctAtom clock counters parameters _ distinct
      (.inr (.inr (.inl ⟨target, name, trigger, rfl⟩)))
  | addColumn target column refuses =>
    exact runStatement_addColumn_rowLocal (atom := Table.RowidsDistinct) clock counters parameters target column refuses
      distinct fun table _ found _ => Table.RowidsDistinct.appendColumns (distinct target table found) _
  | dropColumn position index stored =>
    exact runStatement_dropColumn_satisfies clock counters parameters position index stored distinct fun runs =>
      distinct.dropColumn runs
  | rewrite renamed =>
    exact runStatement_rewrite_satisfies clock counters parameters renamed distinct fun same => distinct.of_outline same
  | drop positions rules =>
    cases rules with
    | none => exact runStatement_drop_rowLocal (atom := Table.RowidsDistinct) clock counters parameters positions distinct
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      exact Effect.satisfies_of_effectDatabase
        (dropKeys_holds rowidsDistinctFacts.laws rules clock positions distinct
          fun _ _ kept => Database.EachTable.drop (atom := Table.RowidsDistinct) kept positions)
  | begin => exact runStatement_writesNone_rowLocal (atom := Table.RowidsDistinct) clock counters parameters distinct _ (by simp)
  | commit => exact runStatement_writesNone_rowLocal (atom := Table.RowidsDistinct) clock counters parameters distinct _ (by simp)
  | rollback => exact runStatement_writesNone_rowLocal (atom := Table.RowidsDistinct) clock counters parameters distinct _ (by simp)
  | prepareError error =>
    exact runStatement_writesNone_rowLocal (atom := Table.RowidsDistinct) clock counters parameters distinct _ (by simp)
  | query query subqueries =>
    exact runStatement_writesNone_rowLocal (atom := Table.RowidsDistinct) clock counters parameters distinct _ (by simp)
  | setting setting on =>
    exact runStatement_writesNone_rowLocal (atom := Table.RowidsDistinct) clock counters parameters distinct _ (by simp)
  | insert target rows returning subqueries rules =>
    cases rules with
    | none => exact runStatement_insert_rowidsDistinct clock counters parameters target rows returning subqueries distinct
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database distinct rfl
      · exact rowsKeys_satisfies rowidsDistinctFacts.laws rules clock target _ distinct _ _
  | update target assignments filter returning subqueries rules =>
    cases rules with
    | none =>
      exact runStatement_update_rowidsDistinct clock counters parameters target assignments filter returning subqueries
        distinct
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database distinct rfl
      · exact rowsKeys_satisfies rowidsDistinctFacts.laws rules _ target _ distinct _ _
  | upsert target rows clauses returning algorithm subqueries rules =>
    cases rules with
    | none =>
      exact runStatement_upsert_rowidsDistinct clock counters parameters target rows clauses returning algorithm subqueries
        distinct
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database distinct rfl
      · exact rowsKeys_satisfies rowidsDistinctFacts.laws rules clock target _ distinct _ _
  | insertSelect target cells query clauses returning algorithm subqueries rules =>
    cases rules with
    | none =>
      exact runStatement_insertSelect_none_satisfies clock counters parameters target cells query clauses returning algorithm subqueries distinct
        fun literals => runStatement_upsert_rowidsDistinct clock counters parameters target literals clauses returning algorithm subqueries
          distinct
    | some rules =>
      exact runStatement_insertSelect_some_satisfies clock counters parameters target cells query clauses returning algorithm subqueries rules distinct
        fun _ _ _ plain conflict => rowsKeys_satisfies rowidsDistinctFacts.laws rules clock target _ distinct plain conflict
  | delete target filter returning subqueries rules =>
    cases rules with
    | none =>
      exact runStatement_delete_tableAtom Table.rowidsDistinctAtom clock counters parameters target filter returning
        subqueries distinct
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database distinct rfl
      · exact rowsKeys_satisfies rowidsDistinctFacts.laws rules _ target _ distinct _ _

end Belay.Sqlite.Model
