import Belay.Sqlite.RunResultSteps

set_option doc.verso true

/-! The execution rule of a SELECT for the run of a script (ADR 0027, D2 and D5): a script of one
SELECT statement that resolves to a query that is ready
({lit}`Belay.Sqlite.Model.Connection.SelectReady`) returns a result with a property exactly when
every result that SQLite may give for it has the property. The rule reads the clock and the
counters of the environment, so it holds for every environment, not only the default one. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- For every script of one statement with its values, database, environment and property
{lit}`Q` of a result: when the statement resolves to a query statement on the new connection
({name}`resolveStatement`), the step runs it at a clock value ({name}`statementClock`), and the
query is ready there ({name}`Connection.SelectReady`) with source rows {lit}`source` and bound
query {lit}`bound`, the run of the script ({name}`send`) returns a result with {lit}`Q`
({name}`Run.returnsResult`) exactly when every result that SQLite may give for {lit}`bound` over
the source rows ({name}`Resolved.Query.possibleResults`) has {lit}`Q`. Proof sketch:
{name}`Run.send_returnsResult_iff` reads the step, and
{name}`runScriptStep_select_returnsResult` its output. -/
theorem Run.send_returnsResult_select {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (db : Database) (env : Env) {query : Resolved.Query}
    {subqueries : List Resolved.Query} {after : ResolveState} {value : Int} {source : Resolved.SourceRows}
    {bound : Resolved.Query}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query subqueries, after))
    (clocked : statementClock env.clock 0 (.query query subqueries) = some value)
    (ready : (db.raw.connection env.counters).SelectReady value parameters query subqueries source bound)
    (property : List (List Value) → Prop) :
    (db.run script env).returnsResult property ↔
      ∀ result ∈ bound.possibleResults
        ((db.raw.connection env.counters).queryContextAt value parameters query subqueries) source.rows,
        property result := by
  have one : script.statements.length = 1 := by rw [head]; rfl
  rw [Run.send_returnsResult_iff one]
  have same : script.statements[0]'(by rw [one]; exact Nat.one_pos) = (statement, parameters) := by simp [head]
  rw [same]
  exact runScriptStep_select_returnsResult runContext env.clock 0 _ statement parameters resolved clocked ready property

/-- For every script of one statement with its values, database, environment and property
{lit}`Q` of a result, under the premises of {name}`Run.send_returnsResult_select`: the run of the
program {name}`query` of the script returns a result with {lit}`Q` exactly when every result that
SQLite may give has {lit}`Q`. Proof sketch: {name}`Run.query_returnsResult_iff` reads the same
step as {name}`Run.send_returnsResult_select`. -/
theorem Run.query_returnsResult_select {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) (db : Database)
    (env : Env) {query : Resolved.Query} {subqueries : List Resolved.Query} {after : ResolveState} {value : Int}
    {source : Resolved.SourceRows} {bound : Resolved.Query}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query subqueries, after))
    (clocked : statementClock env.clock 0 (.query query subqueries) = some value)
    (ready : (db.raw.connection env.counters).SelectReady value parameters query subqueries source bound)
    (property : List (List Value) → Prop) :
    (db.run (Belay.Sqlite.query script one) env).returnsResult property ↔
      ∀ result ∈ bound.possibleResults
        ((db.raw.connection env.counters).queryContextAt value parameters query subqueries) source.rows,
        property result := by
  rw [Run.query_returnsResult_iff one]
  have same : script.statements[0]'(by rw [one]; exact Nat.one_pos) = (statement, parameters) := by simp [head]
  rw [same]
  exact runScriptStep_select_returnsResult runContext env.clock 0 _ statement parameters resolved clocked ready property

/-- For every script of one statement with its values, database, environment, property {lit}`Q`
of a result and property {lit}`E` of a result code: when the statement resolves to a query
statement on the new connection, the step runs it at a clock value with known counters and source
rows {lit}`source`, and a nested subquery has a fallible call, the source possibly fails, or the
run possibly fails, then the run of the script returns neither a result with {lit}`Q` nor an error
with {lit}`E`. Proof sketch: {name}`resolvedStepOutput_select_unready` gives an unmodeled output,
which returns neither. -/
theorem Run.send_unready {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (db : Database) (env : Env) {query : Resolved.Query}
    {subqueries : List Resolved.Query} {after : ResolveState} {value : Int} {source : Resolved.SourceRows}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query subqueries, after))
    (clocked : statementClock env.clock 0 (.query query subqueries) = some value)
    (known : (db.raw.connection env.counters).state.counters.firstUnknown
      (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source ((db.raw.connection env.counters).queryContextAt value parameters query subqueries)
      (db.raw.connection env.counters).state.database = some source)
    (unready : Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = false ∨ source.fault = .may ∨
      (query.run ((db.raw.connection env.counters).queryContextAt value parameters query subqueries)
        source.rows).fault = .may)
    (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run script env).returnsResult property ∧ ¬ (db.run script env).returnsError code := by
  have one : script.statements.length = 1 := by rw [head]; rfl
  rw [Run.send_returnsResult_iff one, Run.send_returnsError_iff one]
  have same : script.statements[0]'(by rw [one]; exact Nat.one_pos) = (statement, parameters) := by simp [head]
  rw [same, runScriptStep_output, resolved]
  dsimp only
  rw [resolvedStepOutput_select_unready env.clock 0 _ parameters clocked known found unready]
  simp [Output.returnsResult, Output.returnsError]

end Belay.Sqlite
