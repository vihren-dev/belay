import Belay.Sqlite.Model.QueryOutputFacts

set_option doc.verso true

/-! The execution rule of a SELECT (ADR 0027, D5): the output of the step of a query statement
that the model describes, with no fault and a bound window, is the output of every result that
SQLite may give ({name}`Belay.Sqlite.Model.Resolved.Query.possibleResults`). Its premises are the
readiness conditions of the step: the source rows, no possible fault of the source or of a
nested subquery, and a run without mismatch, overflow or fault. A pure-value proof cannot drop
them: {name}`Belay.Sqlite.Model.Resolved.Query.outputOn_clean` alone permits a possible fault. -/

namespace Belay.Sqlite.Model

/-- The readiness of a query statement on a connection at a clock value with the values bound to
its parameters ({name}`Connection.queryContextAt`), with its source rows {lit}`source` and its
bound query {lit}`bound`: each field is one condition under which the step outputs every result
that SQLite may give. -/
structure Connection.SelectReady (connection : Connection) (value : Int) (parameters : List Value)
    (query : Resolved.Query) (subqueries : List Resolved.Query) (source : Resolved.SourceRows)
    (bound : Resolved.Query) : Prop where
  /-- Each counter that the statement reads has a known value. -/
  known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none
  /-- The query has the source rows {lit}`source` in the context of the statement. -/
  found : query.source (connection.queryContextAt value parameters query subqueries) connection.state.database =
    some source
  /-- No nested subquery has a fallible call ({name}`Resolved.subqueriesPlain`). -/
  plain : Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true
  /-- The source rows do not possibly fail. -/
  sourceCertain : source.fault ≠ .may
  /-- The window binds to the query {lit}`bound` with the values ({name}`Resolved.Query.bindWindow`). -/
  window : query.bindWindow parameters = some bound
  /-- The run has no window mismatch. -/
  mismatch : (query.run (connection.queryContextAt value parameters query subqueries) source.rows).mismatch = false
  /-- The run has no overflow. -/
  overflow : (query.run (connection.queryContextAt value parameters query subqueries) source.rows).overflow = false
  /-- The run has no fault, neither certain nor possible. -/
  fault : (query.run (connection.queryContextAt value parameters query subqueries) source.rows).fault = .none

/-- Execution rule: for every clock, index, connection, values and query statement that the step
runs at a clock value ({name}`statementClock`) and that is ready there
({name}`Connection.SelectReady`) with source rows {lit}`source` and bound query {lit}`bound`, the
output of the step ({name}`resolvedStepOutput`) is {name}`Output.ofResults` of every result that
SQLite may give for {lit}`bound` over the source rows. Proof sketch:
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
({name}`runScriptStep`) is {name}`Output.ofResults` of every result that SQLite may give. Proof
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

/-- For every resolution context, clock, index, connection, statement, values and property
{lit}`Q` of a result, under the premises of {name}`runScriptStep_select`: the output of the step
returns a result with {lit}`Q` ({name}`Output.returnsResult`) exactly when every result that
SQLite may give has {lit}`Q`. Proof sketch: {name}`Output.returnsResult_ofResults`; the list of
possible results is not empty ({name}`Resolved.Query.possibleResults_ne_nil`). -/
theorem runScriptStep_select_returnsResult (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (connection : Connection) (statement : Syntax.Statement) (parameters : List Value) {query : Resolved.Query}
    {subqueries : List Resolved.Query} {after : ResolveState} {value : Int} {source : Resolved.SourceRows}
    {bound : Resolved.Query}
    (resolved : resolveStatement context connection.resolveState statement = .ok (.query query subqueries, after))
    (clocked : statementClock clock index (.query query subqueries) = some value)
    (ready : connection.SelectReady value parameters query subqueries source bound)
    (property : List (List Value) → Prop) :
    (runScriptStep context clock index connection statement parameters).output.returnsResult property ↔
      ∀ result ∈ bound.possibleResults (connection.queryContextAt value parameters query subqueries) source.rows,
        property result := by
  rw [runScriptStep_select context clock index connection statement parameters resolved clocked ready,
    Output.returnsResult_ofResults]
  exact and_iff_right (Resolved.Query.possibleResults_ne_nil _ _ _)

end Belay.Sqlite.Model
