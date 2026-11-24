import Belay

set_option doc.verso true

/-! The original run contracts follow by obtaining their output from successful resolution. -/

namespace Belay.Sqlite.ReplacedCalmRuns
open Belay.Sqlite.Model

/-- The original {lit}`Run.query_returnsResult_faultless` follows from the same resolution, evaluation and row premises. -/
theorem query_returnsResult_faultless {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) (db : Database)
    (env : Env) {query bound : Resolved.Query} {subqueries : List Resolved.Query} {after : ResolveState}
    {source : Resolved.SourceRows}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query subqueries, after))
    (found : query.source (Resolved.EvalContext.statement parameters db.raw subqueries) db.raw = some source)
    (sourceCertain : source.fault ≠ .may)
    (calm : (Resolved.Statement.query query subqueries).Calm) (single : query.compound = none)
    (window : query.bindWindow parameters = some bound)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate (Resolved.EvalContext.statement parameters db.raw subqueries) row).2 = .none)
    (noOverflow : bound.fails (Resolved.EvalContext.statement parameters db.raw subqueries) source.rows = false)
    (distinct : bound.distinctCertain (Resolved.EvalContext.statement parameters db.raw subqueries) source.rows = true)
    (property : List (List Value) → Prop) :
    (db.run (Belay.Sqlite.query script one) env).returnsResult property ↔
      ∀ result ∈ bound.possibleResults (Resolved.EvalContext.statement parameters db.raw subqueries) source.rows,
        property result := by
  exact Run.query_returnsResult_faultless head one db env (runScriptStep_output_of_resolved resolved) found
    sourceCertain calm single window faultless noOverflow distinct property

/-- The original {lit}`Run.query_returnsResult_compound` follows from the same resolution, evaluation and row premises. -/
theorem query_returnsResult_compound {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) (db : Database)
    (env : Env) {query bound : Resolved.Query} {subqueries : List Resolved.Query} {after : ResolveState}
    {source : Resolved.SourceRows} {compound : Resolved.Compound}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query subqueries, after))
    (calm : (Resolved.Statement.query query subqueries).Calm) (shape : query.compound = some compound)
    (found : query.source (Resolved.EvalContext.statement parameters db.raw subqueries) db.raw = some source)
    (sourceCertain : source.fault ≠ .may) (window : query.bindWindow parameters = some bound)
    (done : ∀ index ∈ compound.terms,
      ((Resolved.EvalContext.statement parameters db.raw subqueries).subqueries index (source.rows.headD [])).ending =
        .done)
    (certain : (compound.combined (Resolved.EvalContext.statement parameters db.raw subqueries)
      (source.rows.headD [])).2 = true)
    (property : List (List Value) → Prop) :
    (db.run (Belay.Sqlite.query script one) env).returnsResult property ↔
      ∀ result ∈ bound.possibleResults (Resolved.EvalContext.statement parameters db.raw subqueries) source.rows,
        property result := by
  exact Run.query_returnsResult_compound head one db env (runScriptStep_output_of_resolved resolved) calm shape
    found sourceCertain window done certain property

/-- The original {lit}`Run.query_returnsResult_calm` follows from the same resolution, evaluation and row premises. -/
theorem query_returnsResult_calm {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) (db : Database)
    (env : Env) {query : Resolved.Query} {after : ResolveState} {source : Resolved.SourceRows}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query [], after))
    (found : query.source (Resolved.EvalContext.bound parameters) db.raw = some source)
    (sourceCertain : source.fault ≠ .may)
    (calm : (Resolved.Statement.query query []).Calm) (single : query.compound = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (noOverflow : query.fails (Resolved.EvalContext.bound parameters) source.rows = false)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters) source.rows = true)
    (property : List (List Value) → Prop) :
    (db.run (Belay.Sqlite.query script one) env).returnsResult property ↔
      ∀ result ∈ query.possibleResults (Resolved.EvalContext.bound parameters) source.rows, property result := by
  exact Run.query_returnsResult_calm head one db env (runScriptStep_output_of_resolved resolved) found sourceCertain
    calm single limitParameter offsetParameter noOverflow distinct property

/-- The original {lit}`Run.query_returnsResult_calmTable` follows from the same resolution, evaluation and row premises. -/
theorem query_returnsResult_calmTable {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) (db : Database)
    (env : Env) {query : Resolved.Query} {after : ResolveState} {position : Nat} {table : Table}
    (resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query query [], after))
    (sources : query.sources = [.first position]) (present : db.raw.table position = some table)
    (calm : (Resolved.Statement.query query []).Calm) (single : query.compound = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (noOverflow : query.fails (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = false)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = true)
    (property : List (List Value) → Prop) :
    (db.run (Belay.Sqlite.query script one) env).returnsResult property ↔
      ∀ result ∈ query.possibleResults (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table),
        property result := by
  exact Run.query_returnsResult_calmTable head one db env (runScriptStep_output_of_resolved resolved) sources
    present calm single limitParameter offsetParameter noOverflow distinct property

#print axioms query_returnsResult_faultless
#print axioms query_returnsResult_compound
#print axioms query_returnsResult_calm
#print axioms query_returnsResult_calmTable

end Belay.Sqlite.ReplacedCalmRuns
