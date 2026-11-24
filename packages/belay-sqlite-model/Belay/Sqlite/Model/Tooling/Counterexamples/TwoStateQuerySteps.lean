import Belay.Sqlite.Model.Programs.StatementRunLaws.SelectCalmRule
import Belay.Sqlite.Model.Schema.Dispatch.TwoStateQuerySteps
import Belay.Sqlite.Model.Schema.Dispatch.ExceptSubqueryRun
import Belay.Sqlite.Model.Queries.Evaluation.SelectSubqueryRules
import Belay.Sqlite.Model.Tooling.Counterexamples.QueryOutputRows

set_option doc.verso true

/-! The output of a calm query statement at each clock, observed with or without an initial database (ADR 0017,
S6). The calm rule {name}`Belay.Sqlite.Model.resolvedStepOutput_calm_unordered` reads a statement without an initial
database. Here the statement is observed with an optional initial database
({name}`Belay.Sqlite.Model.resolvedStepOutput` with {lit}`initial`): a source of the initial origin reads it, and the
subqueries of the statement read it at every depth. The module gives when the output has rows, for each query and for
{lit}`SELECT 1 WHERE c`. -/

namespace Belay.Sqlite.Model

/-- Take a clock, an index, a connection, values, an optional initial database and a calm query statement. Take the
source rows {lit}`source` of its query and its bound window {lit}`bound`. The output of its step has rows exactly when
all of these hold:

* the source rows have no fault {lit}`may`;
* the run of the query has no window mismatch, no overflow and no fault;
* the one result of the bound query has a row.

The query runs in the context of {name}`Connection.queryContextFrom` with the initial database. Proof sketch: unfold
the step. The statement reads no clock and no unknown counter, and its subqueries are plain. Each case of the faults,
the mismatch and the overflow gives an error, an unmodeled output or the results that SQLite may give for the bound
query, and these have rows exactly when the one result has a row ({name}`Output.hasRows_possibleResults`). -/
theorem resolvedStepOutput_calm_hasRows (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) (query bound : Resolved.Query) (subqueries : List Resolved.Query)
    (initial : Option Database) (source : Resolved.SourceRows)
    (calm : (Resolved.Statement.query query subqueries).Calm)
    (found : query.source (connection.queryContextFrom parameters query subqueries initial)
      connection.state.database initial = some source)
    (window : query.bindWindow parameters = some bound) :
    (resolvedStepOutput clock index connection parameters (.query query subqueries) initial).hasRows = true ↔
      source.fault ≠ .may ∧
      (query.run (connection.queryContextFrom parameters query subqueries initial) source.rows).mismatch = false ∧
      (query.run (connection.queryContextFrom parameters query subqueries initial) source.rows).overflow = false ∧
      (query.run (connection.queryContextFrom parameters query subqueries initial) source.rows).fault = .none ∧
      bound.results (connection.queryContextFrom parameters query subqueries initial) source.rows ≠ [] := by
  have hrun : query.runOn 0 (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
      parameters connection.state.database subqueries initial =
      some (source, query.run (connection.queryContextFrom parameters query subqueries initial) source.rows) := by
    simp [Resolved.Query.runOn, found]
  have possible : query.possibleOn 0
      (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads) parameters
      connection.state.database subqueries initial =
      some (bound.possibleResults (connection.queryContextFrom parameters query subqueries initial) source.rows) := by
    simp [Resolved.Query.possibleOn, found, window]
  generalize query.run (connection.queryContextFrom parameters query subqueries initial) source.rows = run at hrun ⊢
  unfold resolvedStepOutput
  simp only [statementClock, calm.readsClock, Bool.false_eq_true, ite_false, calm.firstUnknown]
  simp only [SqlState.statementRun, runStatement, hrun, calm.subqueries_plain, calm.firstUnknown,
    Option.all_some, Bool.and_true, Option.isNone_none]
  unfold Output.ofStep advanceRun advanceWith
  cases source.fault <;> cases fault : run.fault <;> cases mismatch : run.mismatch <;>
    cases overflow : run.overflow <;>
    simp [possibleOutput, queryEffect, SqlState.publish, SqlTransition.counted, haltError_failed, possible,
      mismatch, overflow, fault]
  all_goals try simp [haltError, Output.hasRows_possibleResults]
  all_goals try simp [Output.hasRows]

/-- Take a clock, an index, a connection, values, a condition {lit}`c`, a list of subqueries and an optional initial
database. Let the statement {lit}`SELECT 1 WHERE c` with the subqueries be calm, and let {lit}`c` have no fault over
the row with no cells in the context of the statement ({name}`Connection.queryContextFrom`). Then the output of its
step has rows exactly when {lit}`c` is true over that row. The subqueries can be any queries: the context of the
statement holds their runs. Proof sketch: the query has the one source row with no cells
({name}`Resolved.Query.source_noFrom_from`) and runs without a fault ({name}`Resolved.Query.run_of_faultless`), so
{name}`resolvedStepOutput_calm_hasRows` applies; the one result has a row exactly when {lit}`WHERE` keeps the row
({name}`Resolved.Query.results_eq_nil_iff_plain`). -/
theorem resolvedStepOutput_selectOneWhere_hasRows (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) (condition : Resolved.Expr) (subqueries : List Resolved.Query)
    (initial : Option Database)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere condition) subqueries).Calm)
    (quiet : (condition.evaluate (connection.queryContextFrom parameters (Resolved.Query.selectOneWhere condition)
      subqueries initial) []).2 = .none) :
    (resolvedStepOutput clock index connection parameters (.query (Resolved.Query.selectOneWhere condition) subqueries)
      initial).hasRows = true ↔
      Resolved.truthy (condition.eval (connection.queryContextFrom parameters (Resolved.Query.selectOneWhere condition)
        subqueries initial) []) = true := by
  have faultless : ∀ row ∈ [] :: [[]], ∀ expression ∈ (Resolved.Query.selectOneWhere condition).expressions,
      (expression.evaluate (connection.queryContextFrom parameters (Resolved.Query.selectOneWhere condition)
        subqueries initial) row).2 = .none := by
    intro row member expression inside
    have empty : row = [] := by simpa using member
    subst empty
    exact Resolved.Query.selectOneWhere_faultless _ condition quiet expression inside
  rw [resolvedStepOutput_calm_hasRows clock index connection parameters _ _ subqueries initial _ calm
    (Resolved.Query.source_noFrom_from _ _ _ _ rfl) (Resolved.Query.bindWindow_literal _ _ rfl rfl),
    Resolved.Query.run_of_faultless _ rfl rfl rfl calm.query_plain faultless rfl rfl]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and]
  rw [Resolved.Query.results_eq_nil_iff_plain _ rfl rfl rfl rfl (by simp [Resolved.Query.simple])]
  simp [Resolved.filtered, Resolved.Query.simple, Resolved.Expr.eval]

/-- For every calm query statement observed with an initial database whose run is clean and whose one result has a
row, the output of its step has rows. Proof sketch: {name}`resolvedStepOutput_calm_hasRows`. -/
theorem resolvedStepOutput_query_hasRows_of_clean_from (index : Nat) (connection : Connection)
    (parameters : List Value) (query bound : Resolved.Query) (subqueries : List Resolved.Query) (initial : Database)
    (source : Resolved.SourceRows) (run : Resolved.QueryRun)
    (calm : (Resolved.Statement.query query subqueries).Calm)
    (found : query.source (connection.queryContextFrom parameters query subqueries (some initial))
      connection.state.database (some initial) = some source)
    (window : query.bindWindow parameters = some bound)
    (ran : query.run (connection.queryContextFrom parameters query subqueries (some initial)) source.rows = run)
    (sourceClean : source.fault = .none) (mismatch : run.mismatch = false) (overflow : run.overflow = false)
    (fault : run.fault = .none)
    (results : bound.results (connection.queryContextFrom parameters query subqueries (some initial)) source.rows ≠ []) :
    (resolvedStepOutput none index connection parameters (.query query subqueries) (some initial)).hasRows = true := by
  subst ran
  exact (resolvedStepOutput_calm_hasRows none index connection parameters query bound subqueries (some initial) source
    calm found window).2 ⟨by simp [sourceClean], mismatch, overflow, fault, results⟩

end Belay.Sqlite.Model
