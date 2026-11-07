import Belay.Sqlite.Model.SelectCalmRule

set_option doc.verso true

/-! The overflow rule of a SELECT (ADR 0027, D5): a query statement that the model describes and
whose aggregate certainly overflows ({lit}`Query.fails`) gives the error {lit}`integer overflow`,
not a result. A proof about the values of the query cannot drop the overflow: the value of
{lit}`sum` over rows whose sum leaves the 64-bit range is no result of the statement. -/

namespace Belay.Sqlite.Model

/-- Overflow rule: for every clock, index, connection, values, query that is no compound,
subqueries, source rows {lit}`source` and query {lit}`bound` that the window binds to with the
values, when the step runs the statement at a clock value ({name}`statementClock`), each counter
that it reads is known, the query has the source rows, no nested subquery has a fallible call, the
source does not possibly fail, and {lit}`bound` over the source rows has a failing aggregate
({name}`Resolved.Query.fails`), does not certainly or possibly fail and keeps the same rows for
{lit}`DISTINCT` in every order, then the output of the step ({name}`resolvedStepOutput`) is the
error {lit}`integer overflow`. Proof sketch: {name}`Resolved.Query.run_single` gives a run with no
mismatch, the overflow and no fault, so the model describes the statement
({name}`resolvedStepOutput_query_at`) and its output is the error of the overflow. -/
theorem resolvedStepOutput_select_overflow (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) {query : Resolved.Query} {subqueries : List Resolved.Query} {value : Int}
    {source : Resolved.SourceRows} {bound : Resolved.Query}
    (clocked : statementClock clock index (.query query subqueries) = some value)
    (single : query.compound = none)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (connection.queryContextAt value parameters query subqueries) connection.state.database =
      some source)
    (plain : Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true)
    (sourceCertain : source.fault ≠ .may)
    (window : query.bindWindow parameters = some bound)
    (overflow : bound.fails (connection.queryContextAt value parameters query subqueries) source.rows = true)
    (noMustFail : bound.mustFail (connection.queryContextAt value parameters query subqueries) source.rows = false)
    (noMayFail : bound.mayFail (connection.queryContextAt value parameters query subqueries) source.rows = false)
    (distinct : bound.distinctCertain (connection.queryContextAt value parameters query subqueries) source.rows = true) :
    resolvedStepOutput clock index connection parameters (.query query subqueries) =
      .error ExecutionError.integerOverflow.primaryCode := by
  have run := Resolved.Query.run_single (connection.queryContextAt value parameters query subqueries) query
    source.rows single (by simpa using window)
  rw [noMustFail, noMayFail, distinct, overflow] at run
  have certain : (source.fault != .may) = true := by simpa using sourceCertain
  rw [resolvedStepOutput_query_at clock index connection parameters query subqueries clocked known]
  unfold Resolved.Query.described Resolved.Query.outputOn
  simp only [Resolved.Query.runOn]
  have foundAt : query.source (Resolved.statementContext value
      (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads) parameters
      connection.state.database subqueries) connection.state.database = some source := found
  simp only [foundAt, Option.map_some]
  simp [plain, certain, run]

end Belay.Sqlite.Model
