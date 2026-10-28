import Belay.Sqlite.Model.AdmittedPlainWrites
import Belay.Sqlite.Model.AdmittedRowLaws
import Belay.Sqlite.Model.AdmittedSchemaStatements
import Belay.Sqlite.Model.RowLocalAddColumnTheorems
import Belay.Sqlite.Model.RowLocalSchema
import Belay.Sqlite.Model.RowLocalWrites
import Belay.Sqlite.Model.InsertSelectLaws
import Belay.Sqlite.Model.StatementRewrite
import Belay.Sqlite.Model.StatementDropColumn

set_option doc.verso true

/-! The shared complete statement dispatch for row-local constraints and the five admitted
table atoms. Each caller supplies only the independent write, INSERT-query and column-add facts. For a {lit}`TableAtom` the
statements that write no row, CREATE, DROP and DELETE keep the atom without further facts. ADD COLUMN
and the three forms that compute a row without rules (INSERT, UPDATE and upsert) need a fact of the
atom, so the skeleton takes them as hypotheses and each atom gives them. A statement with rules is
a write of the row engine, which keeps the atom with the laws of {lit}`WriteLaws` (the engine checks
every row that it writes, owner decision M of the status file, finding 16). -/

namespace Belay.Sqlite.Model

/-- For every {name}`TableAtom`, clock value, counters, parameter list, resolved statement and
database: if
* the atom has the laws of {name}`WriteLaws` ({lit}`laws`);
* every table of the database has the atom;
* the ADD COLUMN fact holds: if the statement is ADD COLUMN at a target with a column, the database
  has a table at the target, and a value is an added cell of the table and the column
  ({name}`AddedCell`), then the table with the column and the value appended has the atom;
* the row fact holds: if the statement is an INSERT, UPDATE or upsert without rules, the effect of
  {name}`runStatement` satisfies "every table has the atom";
* the select fact holds: if the statement is an INSERT from a query without rules, the effect of
  {name}`runStatement` satisfies "every table has the atom";

then the effect of {name}`runStatement` satisfies "every table has the atom"
({name}`Effect.Satisfies`): the database of a success and that of an error with
{name}`ExecutionError.constraintFail` have it, and any other error requires nothing. The theorem
covers every form of {name}`Resolved.Statement`. Proof sketch: a case for each form; CREATE, and DROP and
DELETE without rules, use the frame facts of the atom ({name}`runStatement_create_tableAtom`,
{name}`runStatement_drop_rowLocal`, {name}`runStatement_delete_tableAtom`), RENAME is
{name}`runStatement_rewrite_tableAtom`, a statement without writes keeps the
database, ADD COLUMN is {name}`runStatement_addColumn_rowLocal`, and a write with rules is a write of the
row engine ({name}`rowsKeys_satisfies`, {name}`dropKeys_holds`).
The ADD COLUMN premise covers either value of the refusal flag. -/
theorem runStatement_tableAtom {atom : Table → Prop} (tableAtom : TableAtom atom)
    (laws : WriteLaws fun database => database.EachTable atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (statement : Resolved.Statement) {database : Database}
    (every : database.EachTable atom)
    (addColumn : ∀ target column refuses table value, statement = .addColumn target column refuses →
      database.table target = some table → AddedCell table column value → atom (table.appendColumns [(column, value)]))
    (selects : (∃ target cells query clauses returning algorithm subqueries,
        statement = .insertSelect target cells query clauses returning algorithm subqueries none) →
      (runStatement clock counters parameters statement database).effect.Satisfies fun after => after.EachTable atom)
    (writes : ((∃ target rows returning subqueries, statement = .insert target rows returning subqueries none) ∨
      (∃ target assignments filter returning subqueries,
        statement = .update target assignments filter returning subqueries none) ∨
      (∃ target rows clauses returning algorithm subqueries,
        statement = .upsert target rows clauses returning algorithm subqueries none)) →
      (runStatement clock counters parameters statement database).effect.Satisfies fun after => after.EachTable atom) :
    (runStatement clock counters parameters statement database).effect.Satisfies fun after => after.EachTable atom := by
  cases statement with
  | createTable target name shape =>
    exact runStatement_create_tableAtom tableAtom clock counters parameters _ every (.inl ⟨target, name, shape, rfl⟩)
  | createIndex target name index =>
    exact runStatement_create_tableAtom tableAtom clock counters parameters _ every
      (.inr (.inl ⟨target, name, index, rfl⟩))
  | createView target name view =>
    exact runStatement_create_tableAtom tableAtom clock counters parameters _ every
      (.inr (.inr (.inr ⟨target, name, view, rfl⟩)))
  | createTrigger target name trigger =>
    exact runStatement_create_tableAtom tableAtom clock counters parameters _ every
      (.inr (.inr (.inl ⟨target, name, trigger, rfl⟩)))
  | addColumn target column refuses =>
    exact runStatement_addColumn_rowLocal clock counters parameters target column refuses every
      fun table value found added => addColumn target column refuses table value rfl found added
  | dropColumn position index stored =>
    exact runStatement_dropColumn_eachTable tableAtom.dropped tableAtom.renamed clock counters parameters position index stored every
  | rewrite renamed => exact runStatement_rewrite_tableAtom tableAtom clock counters parameters renamed every
  | drop positions rules =>
    cases rules with
    | none => exact runStatement_drop_rowLocal clock counters parameters positions every
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      exact Effect.satisfies_of_effectDatabase
        (dropKeys_holds laws rules clock positions every
          fun _ _ kept => Database.EachTable.drop (atom := atom) kept positions)
  | begin => exact runStatement_writesNone_rowLocal clock counters parameters every _ (by simp)
  | commit => exact runStatement_writesNone_rowLocal clock counters parameters every _ (by simp)
  | rollback => exact runStatement_writesNone_rowLocal clock counters parameters every _ (by simp)
  | prepareError error => exact runStatement_writesNone_rowLocal clock counters parameters every _ (by simp)
  | query query subqueries => exact runStatement_writesNone_rowLocal clock counters parameters every _ (by simp)
  | setting setting on => exact runStatement_writesNone_rowLocal clock counters parameters every _ (by simp)
  | insert target rows returning subqueries rules =>
    cases rules with
    | none => exact writes (.inl ⟨target, rows, returning, subqueries, rfl⟩)
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database every rfl
      · exact rowsKeys_satisfies laws rules clock target _ every _ _
  | update target assignments filter returning subqueries rules =>
    cases rules with
    | none => exact writes (.inr (.inl ⟨target, assignments, filter, returning, subqueries, rfl⟩))
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database every rfl
      · exact rowsKeys_satisfies laws rules _ target _ every _ _
  | upsert target rows clauses returning algorithm subqueries rules =>
    cases rules with
    | none => exact writes (.inr (.inr ⟨target, rows, clauses, returning, algorithm, subqueries, rfl⟩))
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database every rfl
      · exact rowsKeys_satisfies laws rules clock target _ every _ _
  | insertSelect target cells query clauses returning algorithm subqueries rules =>
    cases rules with
    | none => exact selects ⟨target, cells, query, clauses, returning, algorithm, subqueries, rfl⟩
    | some rules =>
      exact runStatement_insertSelect_some_satisfies clock counters parameters target cells query clauses returning algorithm
        subqueries rules every fun _ _ _ plain conflict => rowsKeys_satisfies laws rules clock target _ every plain conflict
  | delete target filter returning subqueries rules =>
    cases rules with
    | none => exact runStatement_delete_tableAtom tableAtom clock counters parameters target filter returning subqueries every
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database every rfl
      · exact rowsKeys_satisfies laws rules _ target _ every _ _

end Belay.Sqlite.Model
