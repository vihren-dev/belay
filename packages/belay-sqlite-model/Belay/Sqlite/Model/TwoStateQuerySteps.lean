import Belay.Sqlite.Model.SelectCalmRule

set_option doc.verso true

/-! The output of a simple query statement that reads the initial database (ADR 0017, S6). The calm
rule {name}`Belay.Sqlite.Model.resolvedStepOutput_calm_unordered` reads a statement without an initial database. Here the statement is observed with an
initial database ({name}`Belay.Sqlite.Model.resolvedStepOutput` with {lit}`some initial`): a source of the initial
origin reads it, and the subqueries of the statement read it at every depth. The output has rows when the run is
clean and the one result of the query has a row. -/

namespace Belay.Sqlite.Model

/-- The context in which a query statement on a connection evaluates its query when it is observed with an initial
database: the clock value 0, the counters that the statement reads, the values bound to its parameters, the database
of the connection, the subqueries, and the initial database ({name}`Resolved.statementContext`). -/
abbrev Connection.queryContextFrom (connection : Connection) (parameters : List Value) (query : Resolved.Query)
    (subqueries : List Resolved.Query) (initial : Database) : Resolved.EvalContext :=
  Resolved.statementContext 0 (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
    parameters connection.state.database subqueries (some initial)

/-- For every calm query statement observed with an initial database, whose query has source rows without a fault
and a bound window, and whose run has no window mismatch, no overflow and no fault, and whose one result has a row,
the output of its step has rows. In plain words: when the model runs the query cleanly and the result is not
empty, the observation sees rows, whatever the other sources are. Proof sketch: unfold the step; the statement
reads no clock and no unknown counter, the model describes the run (no fault {lit}`may`), the run is no error, so
the output is that of the results SQLite may give for the bound query, which has rows exactly when its one result
has ({name}`Output.hasRows_possibleResults`). -/
theorem resolvedStepOutput_query_hasRows_of_clean_from (index : Nat) (connection : Connection)
    (parameters : List Value) (query bound : Resolved.Query) (subqueries : List Resolved.Query) (initial : Database)
    (source : Resolved.SourceRows) (run : Resolved.QueryRun)
    (calm : (Resolved.Statement.query query subqueries).Calm)
    (found : query.source (connection.queryContextFrom parameters query subqueries initial)
      connection.state.database (some initial) = some source)
    (window : query.bindWindow parameters = some bound)
    (ran : query.run (connection.queryContextFrom parameters query subqueries initial) source.rows = run)
    (sourceClean : source.fault = .none) (mismatch : run.mismatch = false) (overflow : run.overflow = false)
    (fault : run.fault = .none)
    (results : bound.results (connection.queryContextFrom parameters query subqueries initial) source.rows ≠ []) :
    (resolvedStepOutput none index connection parameters (.query query subqueries) (some initial)).hasRows = true := by
  have hrun : query.runOn 0 (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
      parameters connection.state.database subqueries (some initial) = some (source, run) := by
    simp [Resolved.Query.runOn, found, ran]
  have possible : query.possibleOn 0
      (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads) parameters
      connection.state.database subqueries (some initial) =
      some (bound.possibleResults (connection.queryContextFrom parameters query subqueries initial) source.rows) := by
    simp [Resolved.Query.possibleOn, found, window]
  unfold resolvedStepOutput
  simp only [statementClock, calm.readsClock, Bool.false_eq_true, ite_false, calm.firstUnknown]
  simp only [SqlState.statementRun, runStatement, hrun, calm.subqueries_plain, sourceClean, fault, calm.firstUnknown,
    Option.all_some, Bool.and_self, Bool.and_true, Option.isNone_none]
  unfold Output.ofStep advanceRun advanceWith
  simp only [possibleOutput, queryEffect, mismatch, overflow, fault]
  simp [SqlState.publish, SqlTransition.counted, haltError, possible]
  exact (Output.hasRows_possibleResults _ _ _).mpr results

end Belay.Sqlite.Model
