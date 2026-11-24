import Belay

set_option doc.verso true

/-! The original run contracts follow by obtaining their output from successful resolution. -/

namespace Belay.Sqlite.ReplacedFailedRuns
open Belay.Sqlite.Model

/-- The original {lit}`Run.send_unready` follows from the same resolution, evaluation and row premises. -/
theorem send_unready {script : Script} {statement : Syntax.Statement} {parameters : List Value}
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
  exact Run.send_unready head db env (runScriptStep_output_of_resolved resolved) clocked known found unready
    property code

/-- The original {lit}`Run.send_mustFail` follows from the same resolution, evaluation and row premises. -/
theorem send_mustFail {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (db : Database) (env : Env) {query : Resolved.Query}
    {subqueries : List Resolved.Query} {after : ResolveState} {value : Int} {source : Resolved.SourceRows}
    {bound : Resolved.Query}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query subqueries, after))
    (single : query.compound = none)
    (clocked : statementClock env.clock 0 (.query query subqueries) = some value)
    (known : (db.raw.connection env.counters).state.counters.firstUnknown
      (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source ((db.raw.connection env.counters).queryContextAt value parameters query subqueries)
      (db.raw.connection env.counters).state.database = some source)
    (plain : Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true)
    (sourceCertain : source.fault ≠ .may)
    (window : query.bindWindow parameters = some bound)
    (noOverflow : bound.fails ((db.raw.connection env.counters).queryContextAt value parameters query subqueries)
      source.rows = false)
    (mustFail : bound.mustFail ((db.raw.connection env.counters).queryContextAt value parameters query subqueries)
      source.rows = true)
    (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run script env).returnsResult property ∧
      ((db.run script env).returnsError code ↔ code ExecutionError.functionError.primaryCode) := by
  exact Run.send_mustFail head db env (runScriptStep_output_of_resolved resolved) single clocked known found plain
    sourceCertain window noOverflow mustFail property code

/-- The original {lit}`Run.query_prepareError` follows from the same resolution, evaluation and row premises. -/
theorem query_prepareError {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) (db : Database)
    (env : Env) {error : PrepareError} {after : ResolveState}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.prepareError error, after))
    (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run (Belay.Sqlite.query script one) env).returnsResult property ∧
      ((db.run (Belay.Sqlite.query script one) env).returnsError code ↔
        code (ExecutionError.prepare error).primaryCode) := by
  exact Run.query_prepareError head one db env (runScriptStep_output_of_resolved resolved) property code

#print axioms send_unready
#print axioms send_mustFail
#print axioms query_prepareError

end Belay.Sqlite.ReplacedFailedRuns
