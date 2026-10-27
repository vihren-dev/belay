import Belay.Sqlite.Model.Laws
import Belay.Sqlite.Model.InsertSelectLaws
import Belay.Sqlite.Model.Resolution.ResolveStateSpec

set_option doc.verso true

/-! One SQL step and the resolution state, the part for a statement that has a literal run: the agreement of a
connection state with a resolution state, and the catalog after a successful step. The steps that advance and halt
are in {lit}`Belay.Sqlite.Model.StepCatalogLaws`. -/

namespace Belay.Sqlite.Model

/-- A connection state agrees with a resolution state when the visible database has the
current catalog of the resolution, and an open transaction's snapshot has the saved
catalog: both are absent, or both are present with equal catalogs. -/
def SqlState.Agrees (sql : SqlState) (state : ResolveState) : Prop :=
  sql.database.catalog = state.catalog ∧ sql.snapshot.map (·.catalog) = state.saved

/-- For every clock value, counters, list of values, statement that is not a setting pragma
({lit}`PRAGMA setting = value`), database and result: if {name}`literalStep` with the values succeeds with the result, then the result's catalog is
{name}`Resolved.Statement.applyCatalog` of the statement on the database's catalog, and the
statement is not transaction control. Proof sketch: CREATE TABLE, CREATE INDEX, CREATE TRIGGER, ADD
COLUMN, RENAME and DROP call the catalog functions, writes store rows only ({name}`Database.setRows`, and the rows
of a write that checks foreign keys over the input catalog, {name}`keyRun_ok_catalog`), a query
returns the database, and every other statement fails. -/
theorem literalStep_success_catalog {clock : Int} {counters : Counters} {parameters : List Value} {statement : Resolved.Statement}
    {database result : Database} (notSetting : ∀ setting on, statement ≠ .setting setting on)
    (success : literalStep clock counters parameters statement database = .ok result) :
    result.catalog = statement.applyCatalog database.catalog ∧ statement.isControl = false := by
  cases statement with
  | setting setting on => exact absurd rfl (notSetting setting on)
  | createTable target name table =>
    simp only [literalStep, runStatement, step] at success
    split at success
    · cases success; exact ⟨rfl, rfl⟩
    · cases success
  | addColumn target column _ =>
    simp only [literalStep, runStatement, step] at success
    split at success
    · cases success
    · repeat' split at success
      all_goals first | (cases success; exact ⟨rfl, rfl⟩) | cases success
  | insert target rows returning subqueries foreignKeys =>
    cases foreignKeys with
    | none =>
      simp only [literalStep, runStatement, insertOutcome, checkedWrite, StatementRun.withKeys, Option.map] at success
      repeat' split at success
      all_goals first | (cases success; exact ⟨rfl, rfl⟩) | cases success
    | some depth =>
      simp only [literalStep, runStatement] at success
      split at success
      · cases success
      · simp only [StatementRun.withKeys, Option.map, insertKeys] at success
        exact ⟨keyRun_ok_catalog success, rfl⟩
  | upsert target rows clauses returning algorithm subqueries foreignKeys =>
    cases foreignKeys with
    | none =>
      simp only [literalStep, runStatement, StatementRun.withKeys, Option.map] at success
      repeat' split at success
      all_goals first | (cases success; exact ⟨rfl, rfl⟩) | cases success
    | some depth =>
      simp only [literalStep, runStatement] at success
      split at success
      · cases success
      · simp only [StatementRun.withKeys, Option.map, insertKeys] at success
        exact ⟨keyRun_ok_catalog success, rfl⟩
  | insertSelect target cells query clauses returning algorithm subqueries foreignKeys =>
    cases foreignKeys with
    | none =>
      rcases runStatement_insertSelect_none clock counters parameters target cells query clauses returning algorithm subqueries
        database with ⟨_, kept⟩ | ⟨literals, same, _⟩
      · simp only [literalStep, kept] at success
        cases success
      · unfold literalStep at success
        rw [same] at success
        simp only [runStatement, StatementRun.withKeys, Option.map] at success
        repeat' split at success
        all_goals first | (cases success; exact ⟨rfl, rfl⟩) | cases success
    | some depth =>
      rcases runStatement_insertSelect_some clock counters parameters target cells query clauses returning algorithm subqueries
        depth database with ⟨_, kept⟩ | ⟨values, policy, multi, plain, conflict, same⟩
      · simp only [literalStep, kept] at success
        cases success
      · unfold literalStep at success
        rw [same] at success
        exact ⟨keyRun_ok_catalog (by simpa only [rowsKeys] using success), rfl⟩
  | update target assignments filter returning subqueries foreignKeys =>
    cases foreignKeys with
    | none =>
      simp only [literalStep, runStatement, checkedWrite, StatementRun.withKeys, Option.map] at success
      repeat' split at success
      all_goals first | (cases success; exact ⟨rfl, rfl⟩) | cases success
    | some depth =>
      simp only [literalStep, runStatement] at success
      split at success
      · cases success
      · simp only [StatementRun.withKeys, Option.map, updateKeys, rowsKeys] at success
        exact ⟨keyRun_ok_catalog success, rfl⟩
  | delete target filter returning subqueries foreignKeys =>
    cases foreignKeys with
    | none =>
      simp only [literalStep, runStatement, StatementRun.withKeys, Option.map] at success
      split at success
      · cases success
      · cases success; exact ⟨rfl, rfl⟩
    | some depth =>
      simp only [literalStep, runStatement] at success
      split at success
      · cases success
      · simp only [StatementRun.withKeys, Option.map, deleteKeys, rowsKeys] at success
        exact ⟨keyRun_ok_catalog success, rfl⟩
  | query query subqueries =>
    simp only [literalStep, runStatement] at success
    cases ran : query.runOn clock counters parameters database subqueries with
    | none => simp only [ran, queryEffect] at success; cases success; exact ⟨rfl, rfl⟩
    | some pair =>
      obtain ⟨_, run⟩ := pair
      simp only [ran, queryEffect] at success
      repeat' split at success
      all_goals first | (cases success; exact ⟨rfl, rfl⟩) | cases success
  | rewrite renamed =>
    simp only [literalStep, runStatement, step] at success
    split at success
    · cases success; exact ⟨rfl, rfl⟩
    · cases success
  | createIndex target name index | createView target name index | createTrigger target name index =>
    simp only [literalStep, runStatement, step] at success
    repeat' split at success
    all_goals first | (cases success; exact ⟨rfl, rfl⟩) | cases success
  | drop positions foreignKeys =>
    cases foreignKeys with
    | none =>
      simp only [literalStep, runStatement, step, StatementRun.withKeys, Option.map] at success
      cases success; exact ⟨rfl, rfl⟩
    | some depth =>
      simp only [literalStep, runStatement, StatementRun.withKeys, Option.map] at success
      exact ⟨dropKeys_ok_catalog success, rfl⟩
  | begin | commit | rollback | prepareError =>
    simp [literalStep, runStatement, step] at success

end Belay.Sqlite.Model
