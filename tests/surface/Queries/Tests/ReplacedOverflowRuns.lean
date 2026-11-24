import Belay

set_option doc.verso true

/-! The original run contracts follow by obtaining their output from successful resolution. -/

namespace Belay.Sqlite.ReplacedOverflowRuns
open Belay.Sqlite.Model

/-- The original {lit}`Run.query_overflow_calmTable` follows from the same resolution, evaluation and row premises. -/
theorem query_overflow_calmTable {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) (db : Database)
    (env : Env) {query : Resolved.Query} {after : ResolveState} {position : Nat} {table : Table}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query [], after))
    (sources : query.sources = [.first position]) (present : db.raw.table position = some table)
    (calm : (Resolved.Statement.query query []).Calm) (single : query.compound = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (overflow : query.fails (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = true)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = true)
    (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run (Belay.Sqlite.query script one) env).returnsResult property ∧
      ((db.run (Belay.Sqlite.query script one) env).returnsError code ↔
        code ExecutionError.integerOverflow.primaryCode) := by
  exact Run.query_overflow_calmTable head one db env (runScriptStep_output_of_resolved resolved) sources present
    calm single limitParameter offsetParameter overflow distinct property code

/-- The original {lit}`Run.query_mismatch` follows from the same resolution, evaluation and row premises. -/
theorem query_mismatch {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) (db : Database)
    (env : Env) {query : Resolved.Query} {subqueries : List Resolved.Query} {after : ResolveState}
    {source : Resolved.SourceRows}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query subqueries, after))
    (calm : (Resolved.Statement.query query subqueries).Calm) (single : query.compound = none)
    (found : query.source (Resolved.EvalContext.statement parameters db.raw subqueries) db.raw = some source)
    (sourceCertain : source.fault ≠ .may) (mismatch : query.bindWindow parameters = none)
    (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run (Belay.Sqlite.query script one) env).returnsResult property ∧
      ((db.run (Belay.Sqlite.query script one) env).returnsError code ↔
        code ExecutionError.datatypeMismatch.primaryCode) := by
  exact Run.query_mismatch head one db env (runScriptStep_output_of_resolved resolved) calm single found
    sourceCertain mismatch property code

#print axioms query_overflow_calmTable
#print axioms query_mismatch

end Belay.Sqlite.ReplacedOverflowRuns
