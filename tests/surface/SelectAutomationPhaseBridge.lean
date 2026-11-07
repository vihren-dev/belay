import SelectAutomationCore

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! ADR 0027's prototype of the execution bridge (deep review, finding 6): D2's observer over
an output, and the quiet premises under which a calm statement of one query over one table
outputs the query's possible results. -/

namespace SelectAutomation
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database


/-- D2's observer prototype: an output satisfies a property of results when it is one result
that has the property ({name}`Output.rows`), or a nonempty list of alternatives
({name}`Output.oneOf`) that all have it. A {name}`Output.done`, {name}`Output.error` or
{name}`Output.unmodeled` output satisfies no property, and so does an empty list of
alternatives. -/
def OutputSatisfies (property : List (List Value) → Prop) : Output → Prop
  | .rows result => property result
  | .oneOf (first :: rest) => ∀ choice ∈ first :: rest, property choice
  | .oneOf [] | .done _ | .error _ | .unmodeled _ => False

/-- For every property and nonempty list of results that all have the property, the output of
the results ({name}`Output.ofResults`) satisfies the property ({name}`OutputSatisfies`). Proof
sketch: the sorted results without repeats are the results, by {name}`Resolved.stableSort_perm`
and {name}`List.mem_eraseDups`; each branch of the output reads them. -/
theorem ofResults_satisfies (property : List (List Value) → Prop) (results : List (List (List Value)))
    (nonempty : results ≠ []) (each : ∀ result ∈ results, property result) :
    OutputSatisfies property (Output.ofResults results) := by
  have member : ∀ result ∈ Resolved.stableSort (fun a b => (compareResults a b).isLE) results.eraseDups,
      property result := fun result h =>
    each result (List.mem_eraseDups.mp ((Resolved.stableSort_perm _ _).mem_iff.mp h))
  have nonnil : Resolved.stableSort (fun a b => (compareResults a b).isLE) results.eraseDups ≠ [] := by
    obtain ⟨result, h⟩ := List.exists_mem_of_ne_nil results nonempty
    exact List.ne_nil_of_mem ((Resolved.stableSort_perm _ _).mem_iff.mpr (List.mem_eraseDups.mpr h))
  unfold Output.ofResults
  split
  · rename_i result sorted
    exact member result (by rw [sorted]; exact List.mem_singleton.mpr rfl)
  · rename_i sorted
    exact absurd sorted nonnil
  · rename_i first second rest sorted
    exact fun choice h => member choice (by rw [sorted]; exact h)


/-- Run rule: for every context, query that is no compound, has no {lit}`DISTINCT` and no window
parameter, whose aggregates do not overflow over the rows ({name}`Resolved.Query.fails`), whose
expressions have no fallible call and no fault over the rows, the run is the one result with no
fault, no overflow and no mismatch. The model law
{name}`Resolved.Query.run_of_faultless` states the same rule. Proof sketch: unfold {name}`Resolved.Query.run`;
{name}`Resolved.Query.bindWindow_literal`, {name}`Resolved.Query.mustFail_of_faultless` and
{name}`Resolved.Query.mayFail_of_faultless` settle each field. -/
theorem run_of_faultless (context : Resolved.EvalContext) (query : Resolved.Query) (rows : List (List Value))
    (single : query.compound = none) (distinct : query.distinct = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (noOverflow : query.fails context rows = false)
    (plain : query.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true)
    (faultless : ∀ row ∈ [] :: rows, ∀ expression ∈ query.expressions, (expression.evaluate context row).2 = .none) :
    query.run context rows =
      { rows := query.results context rows, fault := .none, overflow := false, mismatch := false } := by
  unfold Resolved.Query.run
  simp [single, Resolved.Query.bindWindow_literal context.parameters query limitParameter offsetParameter,
    Resolved.Query.mustFail_of_faultless context query rows faultless,
    Resolved.Query.mayFail_of_faultless context query rows plain faultless, Resolved.Query.distinctCertain, distinct,
    noOverflow]

/-- Statement rule: for every single-statement query script over a database whose statement
resolves to a calm query of one table at a catalog position, with no compound, no
{lit}`DISTINCT`, no window parameter and no aggregate overflow over the table's rows, the run's
outputs are the one output of the query's possible results over the scan of the table with the
values bound to the parameters. Proof sketch: {name}`Script.outputOn_query` and
{name}`Script.query_outputs` reach the step; {name}`resolvedStepOutput_query`,
{name}`Connection.runOn_of_found` with {name}`Resolved.Query.source_first`, and
{name}`Resolved.Query.outputOn_clean` give the output; {name}`run_of_faultless` with
{name}`Resolved.Statement.Calm.faultless_nil` supplies the quiet run, and
{name}`Connection.queryContext_of_quiet` the context. -/
theorem outputs_of_calm_table (script : Script) (db : Database) {statement : Syntax.Statement}
    {parameters : List Value} {after : ResolveState} {position : Nat} {table : Table} (query : Resolved.Query)
    (isQuery : script.isQuery = true)
    (head : script.statements = [(statement, parameters)])
    (resolved : resolveStatement runContext db.raw.connection.resolveState statement = .ok (.query query [], after))
    (sources : query.sources = [.first position])
    (present : db.raw.table position = some table)
    (calm : (Resolved.Statement.query query []).Calm)
    (single : query.compound = none) (distinct : query.distinct = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (noOverflow : query.fails (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = false) :
    (db.run script).outputs =
      [Output.ofResults (query.possibleResults (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table))] := by
  have output := Script.outputOn_query script db statement parameters [] _ [] after head resolved
  rw [Script.query_outputs isQuery db, output]
  have context := Connection.queryContext_of_quiet db.raw.connection parameters query calm.quiet
  have run := run_of_faultless (db.raw.connection.queryContext parameters query []) query (Resolved.sourceRows table)
    single distinct limitParameter offsetParameter (context ▸ noOverflow) calm.query_plain
    (calm.faultless_nil db.raw.connection parameters)
  rw [resolvedStepOutput_query 0 db.raw.connection parameters query [] calm.readsClock (calm.firstUnknown _)]
  have found : ∀ context, query.source context db.raw.connection.state.database =
      some { rows := Resolved.sourceRows table, width := table.shape.columns.length, fault := .none } :=
    fun context => Resolved.Query.source_first context query _ position table sources present
  have hrun := db.raw.connection.runOn_of_found parameters query [] _ (found _)
  have described : query.described 0
      (db.raw.connection.state.counters.view (Resolved.Statement.query query []).counterReads) parameters
      db.raw.connection.state.database [] = true := by
    unfold Resolved.Query.described
    rw [hrun, run]
    simp [calm.subqueries_plain]
  split
  · rw [Resolved.Query.outputOn_clean query 0 _ parameters db.raw.connection.state.database [] _ query (found _)
        (Resolved.Query.bindWindow_literal parameters query limitParameter offsetParameter) (by rw [run]) (by rw [run])
        (by rw [run]; simp)]
    exact congrArg (fun context => [Output.ofResults (query.possibleResults context (Resolved.sourceRows table))]) context
  · rename_i notDescribed
    exact absurd described notDescribed

#print axioms ofResults_satisfies
#print axioms run_of_faultless
#print axioms outputs_of_calm_table

end SelectAutomation
