import Belay.Sqlite.Model.Programs.Claims.QueryOutputRows
import Belay.Sqlite.Model.Schema.Dispatch.QueryOutputFacts

set_option doc.verso true

/-! Complete query output facts, before projecting row and error observations. -/

namespace Belay.Sqlite.Model

/-- For every clock, index, query statement and connection, and every clock value that the step gives
the statement ({name}`statementClock`), when the statement reads no unknown counter: the output of
its step ({name}`resolvedStepOutput`) is the output of the query ({name}`Resolved.Query.outputOn`)
at that clock value if the model describes the statement ({name}`Resolved.Query.described`), and
{name}`Output.unmodeled` otherwise. The query reads the counters of the statement. Proof sketch:
unfold the step at the clock value; {name}`Output.ofStep_query` gives the output. -/
theorem resolvedStepOutput_query_at (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) (query : Resolved.Query) (subqueries : List Resolved.Query) {value : Int}
    (clocked : statementClock clock index (.query query subqueries) = some value)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none) :
    resolvedStepOutput clock index connection parameters (.query query subqueries) =
      if query.described value (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
          parameters connection.state.database subqueries then
        query.outputOn value (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
          parameters connection.state.database subqueries
      else .unmodeled unmodeledHere := by
  unfold resolvedStepOutput
  simp only [clocked, known]
  simp only [SqlState.statementRun, runStatement, Resolved.Query.described, Option.isNone, known]
  by_cases ready : (Resolved.subqueriesPlain (query.nestedSubqueries subqueries) &&
      (query.runOn value (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
        parameters connection.state.database subqueries).all fun (source, run) =>
        source.fault != .may && run.fault != .may) = true
  · simp only [ready, Bool.and_true, Bool.not_true, ite_true]
    exact Output.ofStep_query query subqueries value index parameters connection.state _ rfl
  · simp [ready]

/-- For every query statement, the output of its step in a run without a clock
({name}`resolvedStepOutput`) is, when the statement reads no clock and no unknown counter, the output
of the query ({name}`Resolved.Query.outputOn`) if the model describes the statement
({name}`Resolved.Query.described`) and {name}`Output.unmodeled` otherwise. The query runs at the clock
value 0 with the counters that it reads. Proof sketch: {name}`resolvedStepOutput_query_at`; the clock
value of a statement that reads no clock is 0. -/
theorem resolvedStepOutput_query (index : Nat) (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (subqueries : List Resolved.Query)
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none) :
    resolvedStepOutput none index connection parameters (.query query subqueries) =
      if query.described 0 (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
          parameters connection.state.database subqueries then
        query.outputOn 0 (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads)
          parameters connection.state.database subqueries
      else .unmodeled unmodeledHere :=
  resolvedStepOutput_query_at none index connection parameters query subqueries
    (by simp [statementClock, noClock]) known

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
