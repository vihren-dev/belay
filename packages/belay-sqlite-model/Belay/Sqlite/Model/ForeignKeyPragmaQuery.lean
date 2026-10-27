import Belay.Sqlite.Model.ForeignKeyCheckLaws
import Belay.Sqlite.Model.ForeignKeyPrepareLaws
import Belay.Sqlite.Model.SimpleQuerySteps

set_option doc.verso true

/-! Foreign-key pragma row generation connected to the query statement that executes it.
Preparation remains a separate condition; empty generated rows do not establish compatible
parent schemas. -/

namespace Belay.Sqlite.Model

/-- The foreign-key pragma selects its four columns without grouping, order or window. -/
theorem keyCheckQuery_simple (table : Option Nat) :
    (pragmaQuery (.foreignKeyCheck table) foreignKeyCheckNames).Simple :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The foreign-key pragma reads only columns, so no expression fails or reads external state. -/
theorem keyCheckQuery_calm (table : Option Nat) : (keyCheckQuery table).Calm := by
  intro expression member
  simp [keyCheckQuery, pragmaQuery, Resolved.Statement.clockExpressions, Resolved.Query.expressions,
    Resolved.Query.keptExpressions, Resolved.QuerySource.expressions, Resolved.Output.scalars,
    Resolved.Output.operands, foreignKeyCheckNames, List.range_succ] at member
  rcases member with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, fun _ => rfl⟩

/-- When the pragma supplies rows, its single source gives those rows without a fault. -/
theorem keyCheckQuery_source (context : Resolved.EvalContext) (database : Database)
    (table : Option Nat) (rows : List (List Value))
    (found : (Resolved.PragmaRows.foreignKeyCheck table).rowsOn database = some rows) :
    (pragmaQuery (.foreignKeyCheck table) foreignKeyCheckNames).source context database =
      some { rows, width := 4, fault := .none } := by
  simp [pragmaQuery, Resolved.Query.source, Resolved.QuerySource.join, found, List.foldlM,
    Resolved.joinRows, Resolved.joinRow, Resolved.joinMatches, Resolved.QuerySource.matches,
    Resolved.PragmaRows.width]

/-- For every connection, table choice, statement index and bound values, the resolved
foreign-key pragma has no rows exactly when its generated rows are the empty list. A missing
generation result is unmodeled and does not count as empty. This concerns the prepared query;
the catalog mismatch check is separate. Proof sketch: the pragma is a calm simple query;
its source is exactly the generated rows, and it has no WHERE condition. -/
theorem resolvedStepOutput_keyCheck_hasNoRows (index : Nat) (connection : Connection)
    (parameters : List Value) (table : Option Nat) :
    (resolvedStepOutput none index connection parameters (keyCheckQuery table)).hasNoRows = true ↔
      (Resolved.PragmaRows.foreignKeyCheck table).rowsOn connection.state.database = some [] := by
  let query := pragmaQuery (.foreignKeyCheck table) foreignKeyCheckNames
  change (resolvedStepOutput none index connection parameters (.query query [])).hasNoRows = true ↔ _
  have calm := keyCheckQuery_calm table
  cases found : (Resolved.PragmaRows.foreignKeyCheck table).rowsOn connection.state.database with
  | none =>
    rw [resolvedStepOutput_query index connection parameters query [] calm.readsClock (calm.firstUnknown _)]
    have source : query.source (connection.queryContext parameters query []) connection.state.database = none := by
      simp [query, pragmaQuery, Resolved.Query.source, Resolved.QuerySource.join, found, List.foldlM]
    have ran : query.runOn 0 (connection.state.counters.view (Resolved.Statement.query query []).counterReads)
        parameters connection.state.database [] = none := by
      change (query.source (connection.queryContext parameters query []) connection.state.database).map _ = none
      rw [source]
      rfl
    simp only [Resolved.Query.described, Resolved.Query.outputOn, ran]
    split <;> simp [Output.hasNoRows]
  | some rows =>
    have source := keyCheckQuery_source (connection.queryContext parameters query []) connection.state.database table rows found
    have empty := resolvedStepOutput_simple_hasNoRows index connection parameters query (keyCheckQuery_simple table)
      { rows, width := 4, fault := .none } calm source rfl
    simpa [query, pragmaQuery, found, List.eq_nil_iff_forall_not_mem] using empty

/-- Canonical result output collapses any nonempty list of empty alternatives to one empty result. -/
private theorem ofResults_empty (results : List (List (List Value)))
    (empty : (Output.ofResults results).hasNoRows = true) : Output.ofResults results = .rows [] := by
  obtain ⟨nonempty, each⟩ := (Output.hasNoRows_ofResults results).mp empty
  cases results with
  | nil => contradiction
  | cons first rest =>
    have firstEmpty := each first (by simp)
    subst first
    have filtered : (rest.filter fun result => !result.isEmpty) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro result member
      simp [each result (by simp [member])]
    have erased : ([] :: rest).eraseDups = [[]] := by simp [List.eraseDups_cons, filtered]
    simp [Output.ofResults, erased, Resolved.stableSort, Resolved.insertStable]

/-- For every connection, table choice, statement index and values, the prepared foreign-key
pragma returns exactly one empty row result if and only if its generated rows are empty.
An error or model restriction never satisfies either side. Proof sketch: the no-row law above,
then the canonical query output collapses empty alternatives to one empty result. -/
theorem resolvedStepOutput_keyCheck_empty (index : Nat) (connection : Connection)
    (parameters : List Value) (table : Option Nat) :
    resolvedStepOutput none index connection parameters (keyCheckQuery table) = .rows [] ↔
      (Resolved.PragmaRows.foreignKeyCheck table).rowsOn connection.state.database = some [] := by
  constructor
  · intro empty
    apply (resolvedStepOutput_keyCheck_hasNoRows index connection parameters table).mp
    rw [empty]
    rfl
  · intro generated
    have empty := (resolvedStepOutput_keyCheck_hasNoRows index connection parameters table).mpr generated
    let query := pragmaQuery (.foreignKeyCheck table) foreignKeyCheckNames
    change (resolvedStepOutput none index connection parameters (.query query [])).hasNoRows = true at empty
    change resolvedStepOutput none index connection parameters (.query query []) = .rows []
    have calm := keyCheckQuery_calm table
    rw [resolvedStepOutput_query index connection parameters query [] calm.readsClock (calm.firstUnknown _)] at empty ⊢
    split at empty
    · simp_all only [ite_true]
      unfold Resolved.Query.outputOn at empty ⊢
      repeat' split at empty
      all_goals simp_all only [Output.hasNoRows, Bool.false_eq_true, ite_false]
      all_goals exact ofResults_empty _ empty
    · simp [Output.hasNoRows] at empty

/-- For every clock, index, connection, values and table choice, the foreign-key pragma
has the same resolved output as a run without a clock. It reads no clock expression.
Proof sketch: the clock guard therefore supplies 0 in both executions. -/
theorem resolvedStepOutput_keyCheck_clock (clock : Option Clock) (index : Nat)
    (connection : Connection) (parameters : List Value) (table : Option Nat) :
    resolvedStepOutput clock index connection parameters (keyCheckQuery table) =
      resolvedStepOutput none index connection parameters (keyCheckQuery table) := by
  simp only [resolvedStepOutput, statementClock, (keyCheckQuery_calm table).readsClock,
    Bool.false_eq_true, ite_false]

end Belay.Sqlite.Model
