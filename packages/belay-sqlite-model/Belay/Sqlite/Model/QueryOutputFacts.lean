import Belay.Sqlite.Model.QueryOutputRows

set_option doc.verso true

/-! Complete query output facts, before projecting row and error observations. -/

namespace Belay.Sqlite.Model

/-- Normalizing result rows preserves whether the result is empty. Proof sketch: normalization
preserves the row count, and a list is empty exactly when that count is zero. -/
theorem Resolved.normalForm_eq_nil (rows : List (List Value)) :
    Resolved.normalForm rows = [] ↔ rows = [] := by
  rw [← List.length_eq_zero_iff, Resolved.normalForm_length, List.length_eq_zero_iff]

/-- Whether the model describes a query statement on a database, with the counters that it reads: its
subqueries (those that are no term of a compound) have no fallible call, and neither the source
rows nor the run of the query have the fault {name}`Resolved.Fault.may`. It is the support check of
{name}`runStatement` for a query. -/
def Resolved.Query.described (query : Resolved.Query) (clock : Int) (counters : Counters) (parameters : List Value)
    (database : Database) (subqueries : List Resolved.Query) : Bool :=
  Resolved.subqueriesPlain (query.nestedSubqueries subqueries) &&
    (query.runOn clock counters parameters database subqueries).all fun (source, run) =>
      source.fault != .may && run.fault != .may

/-- For every query statement, the output of its step in a run without a clock
({name}`resolvedStepOutput`) is, when the statement reads no clock and no unknown counter, the output
of the query ({name}`Resolved.Query.outputOn`) if the model describes the statement
({name}`Resolved.Query.described`) and {name}`Output.unmodeled` otherwise. The query runs at the clock
value 0 with the counters that it reads. Proof sketch: unfold the step; the clock value of a
statement that reads no clock is 0, and {name}`Output.ofStep_query` gives the output. -/
theorem resolvedStepOutput_query (index : Nat) (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (subqueries : List Resolved.Query)
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none) :
    resolvedStepOutput none index connection parameters (.query query subqueries) =
      if query.described 0 (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
          parameters connection.state.database subqueries then
        query.outputOn 0 (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
          parameters connection.state.database subqueries
      else .unmodeled unmodeledHere := by
  unfold resolvedStepOutput
  simp only [statementClock, noClock, Bool.false_eq_true, ite_false, known]
  simp only [SqlState.statementRun, runStatement, Resolved.Query.described, Option.isNone, known]
  by_cases ready : (Resolved.subqueriesPlain (query.nestedSubqueries subqueries) &&
      (query.runOn 0 (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
        parameters connection.state.database subqueries).all fun (source, run) =>
        source.fault != .may && run.fault != .may) = true
  · simp only [ready, Bool.and_true, Bool.not_true, ite_true]
    exact Output.ofStep_query query subqueries 0 index parameters connection.state _ rfl
  · simp [ready]

/-- The context in which a query statement evaluates its query on the connection, without a clock:
the clock value 0, the counters that the statement reads, the values bound to its parameters, the
database of the connection and the subqueries ({name}`Resolved.statementContext`). -/
abbrev Connection.queryContext (connection : Connection) (parameters : List Value) (query : Resolved.Query)
    (subqueries : List Resolved.Query) : Resolved.EvalContext :=
  Resolved.statementContext 0 (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
    parameters connection.state.database subqueries

/-- For every query statement whose query has source rows {lit}`source`, the run of the query on the
connection is the run over these rows. Proof sketch: unfold {name}`Resolved.Query.runOn` and rewrite
with the hypothesis {lit}`found`. -/
theorem Connection.runOn_of_found (connection : Connection) (parameters : List Value) (query : Resolved.Query)
    (subqueries : List Resolved.Query) (source : Resolved.SourceRows)
    (found : query.source (connection.queryContext parameters query subqueries) connection.state.database = some source) :
    query.runOn 0 (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
      parameters connection.state.database subqueries =
      some (source, query.run (connection.queryContext parameters query subqueries) source.rows) := by
  simp [Resolved.Query.runOn, found]

/-- For each clock-free query with known counters and an existing source, the complete output
first checks support, then datatype mismatch, overflow and function failure, in that order.
After these checks, an unbound window gives an unmodeled output; a bound window gives all its
possible results. No source cleanliness or successful window binding is assumed.
Proof sketch: unfold the query output after substituting the source; split on window binding. -/
theorem resolvedStepOutput_query_source (index : Nat) (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (subqueries : List Resolved.Query) (source : Resolved.SourceRows)
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (connection.queryContext parameters query subqueries) connection.state.database = some source) :
    let context := connection.queryContext parameters query subqueries
    let run := query.run context source.rows
    resolvedStepOutput none index connection parameters (.query query subqueries) =
      if Resolved.subqueriesPlain (query.nestedSubqueries subqueries) &&
          (source.fault != .may && run.fault != .may) then
        if run.mismatch then .error ExecutionError.datatypeMismatch.primaryCode
        else if run.overflow then .error ExecutionError.integerOverflow.primaryCode
        else if run.fault == .must then .error ExecutionError.functionError.primaryCode
        else match query.bindWindow parameters with
          | none => .unmodeled "the model gives no result for this query"
          | some bound => Output.ofResults (bound.possibleResults context source.rows)
      else .unmodeled unmodeledHere := by
  rw [resolvedStepOutput_query index connection parameters query subqueries noClock known]
  simp only [Resolved.Query.described, Resolved.Query.outputOn, Resolved.Query.runOn,
    Resolved.Query.possibleOn, found, Option.bind_some]
  cases query.bindWindow parameters <;> rfl

end Belay.Sqlite.Model
