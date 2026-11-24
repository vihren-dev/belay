import Belay

set_option doc.verso true

/-! The original run contracts follow by obtaining their output from successful resolution. -/

namespace Belay.Sqlite.ReplacedSelectRuns
open Belay.Sqlite.Model

/-- The original {lit}`Run.send_returnsResult_select` follows from the same resolution, evaluation and row premises. -/
theorem send_returnsResult_select {script : Script} {statement : Syntax.Statement} {parameters : List Value}
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
  exact Run.send_returnsResult_select head db env (runScriptStep_output_of_resolved resolved) clocked ready property

/-- The original {lit}`Run.query_returnsResult_select` follows from the same resolution, evaluation and row premises. -/
theorem query_returnsResult_select {script : Script} {statement : Syntax.Statement} {parameters : List Value}
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
  exact Run.query_returnsResult_select head one db env (runScriptStep_output_of_resolved resolved) clocked ready
    property

#print axioms send_returnsResult_select
#print axioms query_returnsResult_select

end Belay.Sqlite.ReplacedSelectRuns
