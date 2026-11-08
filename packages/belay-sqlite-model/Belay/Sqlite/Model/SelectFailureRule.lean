import Belay.Sqlite.Model.SelectRunRule

set_option doc.verso true

/-! The failure rule of a SELECT (ADR 0027, D5): a query statement that the model describes and
whose run certainly fails ({lit}`Query.mustFail`) outputs the error of a failing function. It is
the error counterpart of the execution rule: the readiness premises stay, but the run has the
fault {lit}`Fault.must` in place of no fault. A call such as {lit}`abs(-9223372036854775808)`,
whose argument is known, fails in this way. -/

namespace Belay.Sqlite.Model

/-- Failure rule: for every clock, index, connection, values and query statement that is no
compound and that the step runs at a clock value ({name}`statementClock`), with known counters,
source rows {lit}`source` and a window that binds to the query {lit}`bound`: when no nested
subquery has a fallible call ({name}`Resolved.subqueriesPlain`), the source does not possibly fail,
{lit}`bound` over the source rows has no failing aggregate ({name}`Resolved.Query.fails`) and
certainly fails ({name}`Resolved.Query.mustFail`), the output of the step
({name}`resolvedStepOutput`) is the error of a failing function. Whether {lit}`bound` also possibly
fails does not matter. Proof sketch: {name}`Resolved.Query.run_single` gives the fault
{lean}`Resolved.Fault.must` and no overflow, so the model describes the statement, and
{name}`Resolved.Query.outputOn_function` gives the error. -/
theorem resolvedStepOutput_select_mustFail (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) {query : Resolved.Query} {subqueries : List Resolved.Query} {value : Int}
    {source : Resolved.SourceRows} {bound : Resolved.Query}
    (single : query.compound = none)
    (clocked : statementClock clock index (.query query subqueries) = some value)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (connection.queryContextAt value parameters query subqueries) connection.state.database =
      some source)
    (plain : Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true)
    (sourceCertain : source.fault ≠ .may)
    (window : query.bindWindow parameters = some bound)
    (noOverflow : bound.fails (connection.queryContextAt value parameters query subqueries) source.rows = false)
    (mustFail : bound.mustFail (connection.queryContextAt value parameters query subqueries) source.rows = true) :
    resolvedStepOutput clock index connection parameters (.query query subqueries) =
      .error ExecutionError.functionError.primaryCode := by
  have run := Resolved.Query.run_single (connection.queryContextAt value parameters query subqueries) query source.rows
    single (by simpa using window)
  rw [resolvedStepOutput_query_at clock index connection parameters query subqueries clocked known]
  have described : query.described value
      (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads) parameters
      connection.state.database subqueries = true := by
    have certain : (source.fault != .may) = true := by simpa using sourceCertain
    unfold Resolved.Query.described
    simp only [Resolved.Query.runOn]
    rw [found]
    simp [plain, certain, run, mustFail]
  simp only [described, ite_true]
  exact Resolved.Query.outputOn_function query value _ parameters connection.state.database subqueries source found
    (by rw [run]) (by rw [run]; exact noOverflow) (by rw [run]; simp [mustFail])

end Belay.Sqlite.Model
