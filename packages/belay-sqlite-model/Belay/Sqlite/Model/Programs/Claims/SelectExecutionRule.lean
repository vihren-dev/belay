import Belay.Sqlite.Model.Programs.Scripts.QueryOutputFacts
import Belay.Sqlite.Model.Schema.Dispatch.SelectExecutionRule

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Execution rule: for every clock, index, connection, values and query statement that the step
runs at a clock value ({name}`statementClock`) and that is ready there
({name}`Connection.SelectReady`) with source rows {lit}`source` and bound query {lit}`bound`, the
output of the step ({name}`resolvedStepOutput`) is {name}`Output.ofResults` of every result that
the model permits for {lit}`bound` over the source rows. Proof sketch:
{name}`resolvedStepOutput_query_at`; the readiness gives {name}`Resolved.Query.described`, and
{name}`Resolved.Query.outputOn_clean` the output. -/
theorem resolvedStepOutput_select (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) {query : Resolved.Query} {subqueries : List Resolved.Query} {value : Int}
    {source : Resolved.SourceRows} {bound : Resolved.Query}
    (clocked : statementClock clock index (.query query subqueries) = some value)
    (ready : connection.SelectReady value parameters query subqueries source bound) :
    resolvedStepOutput clock index connection parameters (.query query subqueries) =
      Output.ofResults (bound.possibleResults (connection.queryContextAt value parameters query subqueries) source.rows) := by
  rw [resolvedStepOutput_query_at clock index connection parameters query subqueries clocked ready.known]
  have described : query.described value
      (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads) parameters
      connection.state.database subqueries = true := by
    have certain : (source.fault != .may) = true := by simpa using ready.sourceCertain
    unfold Resolved.Query.described
    simp only [Resolved.Query.runOn]
    rw [ready.found]
    simp [ready.plain, certain, ready.fault]
  simp only [described, ite_true]
  exact Resolved.Query.outputOn_clean query value _ parameters connection.state.database subqueries source bound
    ready.found ready.window ready.mismatch ready.overflow (by rw [ready.fault]; decide)

/-- For every result, the output of the only possible result is that result as rows. Proof sketch:
one result has no repeat, and the sort of one item keeps it. -/
theorem Output.ofResults_singleton (result : List (List Value)) : Output.ofResults [result] = .rows result := by
  have erased : [result].eraseDups = [result] := by simp [List.eraseDups_cons]
  simp [Output.ofResults, erased, Resolved.stableSort, Resolved.insertStable]

/-- Unordered execution rule: for every clock, index, connection, values and query statement that
is ready ({name}`Connection.SelectReady`) at its clock value with source rows {lit}`source` and a
bound query {lit}`bound` without {lit}`ORDER BY`, {lit}`OFFSET` and {lit}`LIMIT`, the output of the
step is the rows of {lit}`bound` over the source rows, in normal form. Proof sketch:
{name}`resolvedStepOutput_select` with the one permitted result
({name}`Resolved.Query.possibleResults_unordered`, {name}`Output.ofResults_singleton`). -/
theorem resolvedStepOutput_select_unordered (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) {query : Resolved.Query} {subqueries : List Resolved.Query} {value : Int}
    {source : Resolved.SourceRows} {bound : Resolved.Query}
    (clocked : statementClock clock index (.query query subqueries) = some value)
    (ready : connection.SelectReady value parameters query subqueries source bound)
    (unordered : bound.orderBy = []) (noOffset : bound.offset = 0) (noLimit : bound.limit = none) :
    resolvedStepOutput clock index connection parameters (.query query subqueries) =
      .rows (Resolved.normalForm (bound.results (connection.queryContextAt value parameters query subqueries)
        source.rows)) := by
  rw [resolvedStepOutput_select clock index connection parameters clocked ready,
    Resolved.Query.possibleResults_unordered _ unordered noOffset noLimit, Output.ofResults_singleton]

/-- Unready rule: for every clock, index, connection, values and query statement that the step
runs at a clock value ({name}`statementClock`), with known counters and source rows
{lit}`source`, when a nested subquery has a fallible call ({name}`Resolved.subqueriesPlain`), the
source possibly fails, or the run possibly fails, the output of the step is
{name}`Output.unmodeled`, whatever the values of the query. This holds also when
{name}`Resolved.Query.outputOn` gives rows. Proof sketch: {name}`resolvedStepOutput_query_at`;
each case makes {name}`Resolved.Query.described` false. -/
theorem resolvedStepOutput_select_unready (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) {query : Resolved.Query} {subqueries : List Resolved.Query} {value : Int}
    {source : Resolved.SourceRows}
    (clocked : statementClock clock index (.query query subqueries) = some value)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (connection.queryContextAt value parameters query subqueries) connection.state.database =
      some source)
    (unready : Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = false ∨ source.fault = .may ∨
      (query.run (connection.queryContextAt value parameters query subqueries) source.rows).fault = .may) :
    resolvedStepOutput clock index connection parameters (.query query subqueries) = .unmodeled unmodeledHere := by
  rw [resolvedStepOutput_query_at clock index connection parameters query subqueries clocked known]
  have described : query.described value
      (connection.state.counters.view (Resolved.Statement.query query subqueries).counterReads) parameters
      connection.state.database subqueries = false := by
    unfold Resolved.Query.described
    simp only [Resolved.Query.runOn]
    rw [found]
    rcases unready with reason | reason | reason <;> simp [reason]
  simp [described]

/-- Execution rule of a step: for every resolution context, clock, index, connection, statement
and values, when resolution gives a query statement ({name}`resolveStatement`) that the step runs
at a clock value and that is ready there ({name}`Connection.SelectReady`), the output of the step
({name}`runScriptStep`) is {name}`Output.ofResults` of every result that the model permits. Proof
sketch: {name}`runScriptStep_output` and {name}`resolvedStepOutput_select`. -/
theorem runScriptStep_select (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (connection : Connection) (statement : Syntax.Statement) (parameters : List Value) {query : Resolved.Query}
    {subqueries : List Resolved.Query} {after : ResolveState} {value : Int} {source : Resolved.SourceRows}
    {bound : Resolved.Query}
    (resolved : resolveStatement context connection.resolveState statement = .ok (.query query subqueries, after))
    (clocked : statementClock clock index (.query query subqueries) = some value)
    (ready : connection.SelectReady value parameters query subqueries source bound) :
    (runScriptStep context clock index connection statement parameters).output =
      Output.ofResults (bound.possibleResults (connection.queryContextAt value parameters query subqueries) source.rows) := by
  rw [runScriptStep_output, resolved]
  exact resolvedStepOutput_select clock index connection parameters clocked ready

end Belay.Sqlite.Model
