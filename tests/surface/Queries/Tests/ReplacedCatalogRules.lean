import Belay

set_option doc.verso true

/-! Original catalog contracts for ADR 0033. Each proof obtains the output equality from
the fixed catalog and applies the rule that reasons about the runtime rows. -/

namespace Belay.Sqlite.ReplacedCatalog
open Belay.Sqlite.Model

/-- For every database {lit}`db`, database {lit}`catalog` whose catalog {lit}`db` has, counters,
statement, query and subqueries: when the statement resolves on {lit}`catalog` to the query with the
subqueries ({name}`Database.selectQuery?`), it resolves to them on the connection of {lit}`db` with the
counters, with some state after it. Proof sketch: the resolution reads only the catalog
({name}`Database.resolveState_of_catalog`); the cases of {name}`Database.selectQuery?`. -/
theorem resolve_of_selectQuery {db catalog : Database} (schema : db.HasCatalog catalog)
    (counters : Counters) {statement : Syntax.Statement} {query : Resolved.Query}
    {subqueries : List Resolved.Query} (resolved : catalog.selectQuery? statement = some (query, subqueries)) :
    ∃ after, resolveStatement runContext (db.raw.connection counters).resolveState statement =
      .ok (.query query subqueries, after) := by
  rw [Database.resolveState_of_catalog db catalog schema]
  unfold Database.selectQuery? at resolved
  split at resolved
  · cases resolved
    exact ⟨_, ‹_›⟩
  all_goals cases resolved

/-- The former {lit}`Sql.check_query_ofResolveState` with the same catalog, scan and result premises. -/
theorem check_query_ofResolveState {script : Script} {one : script.statements.length = 1}
    {statement : Syntax.Statement} {parameters : List Value} (select : script.isSelect = true)
    (head : script.statements = [(statement, parameters)]) {state : ExecutionContext} {catalog : Database}
    (connection : state.connection.resolveState = (catalog.raw.connection {}).resolveState)
    {query : Resolved.Query} {position : Nat} {shape : CatalogTable}
    (resolved : catalog.selectQuery? statement = some (query, []))
    (sources : query.sources = [.first position])
    (present : catalog.raw.catalog.tableAt position = some shape)
    (calm : (Resolved.Statement.query query []).Calm) (single : query.compound = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (noOverflow : query.fails (Resolved.EvalContext.bound parameters)
      (Resolved.sourceRows { shape, rows := state.connection.state.database.rows.getD position [] }) = false)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters)
      (Resolved.sourceRows { shape, rows := state.connection.state.database.rows.getD position [] }) = true)
    {post : Except Nat (List (List Value)) → ExecutionContext → Prop}
    (each : ∀ result ∈ query.possibleResults (Resolved.EvalContext.bound parameters)
        (Resolved.sourceRows { shape, rows := state.connection.state.database.rows.getD position [] }),
      ∀ final : ExecutionContext, final.connection = state.connection → post (.ok result) final) :
    (Belay.Sqlite.query script one).check post state := by
  obtain ⟨_, found⟩ := resolve_of_selectQuery (db := catalog) rfl {} resolved
  refine Sql.check_query_catalog_rows_at select head connection ?_ sources present calm single limitParameter offsetParameter noOverflow distinct each
  simp [statementOutputAt, found]

/-- The former {lit}`Sql.check_query_ofCatalog` with the same catalog, scan and result premises. -/
theorem check_query_ofCatalog {script : Script} {one : script.statements.length = 1}
    {statement : Syntax.Statement} {parameters : List Value} (select : script.isSelect = true)
    (head : script.statements = [(statement, parameters)]) {state : ExecutionContext} {db : Database}
    {counters : Counters} (connected : state.connection = db.raw.connection counters) {catalog : Database}
    (schema : db.HasCatalog catalog) {query : Resolved.Query} {position : Nat} {shape : CatalogTable}
    (resolved : catalog.selectQuery? statement = some (query, []))
    (sources : query.sources = [.first position])
    (present : catalog.raw.catalog.tableAt position = some shape)
    (calm : (Resolved.Statement.query query []).Calm) (single : query.compound = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (noOverflow : query.fails (Resolved.EvalContext.bound parameters) (db.scanAt position) = false)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters) (db.scanAt position) = true)
    {post : Except Nat (List (List Value)) → ExecutionContext → Prop}
    (each : ∀ result ∈ query.possibleResults (Resolved.EvalContext.bound parameters) (db.scanAt position),
      ∀ final : ExecutionContext, final.connection = state.connection → post (.ok result) final) :
    (Belay.Sqlite.query script one).check post state := by
  obtain ⟨_, found⟩ := resolve_of_selectQuery (db := catalog) rfl {} resolved
  refine Sql.check_query_catalog_rows select head connected schema ?_ sources present calm single limitParameter offsetParameter noOverflow distinct each
  simp [statementOutputAt, found]

/-- The former {lit}`Run.query_returnsResult_ofCatalog` with the same catalog, scan and result premises. -/
theorem query_returnsResult_ofCatalog {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) {db : Database}
    (env : Env) {catalog : Database} (schema : db.HasCatalog catalog) {query : Resolved.Query} {position : Nat}
    {shape : CatalogTable}
    (resolved : catalog.selectQuery? statement = some (query, []))
    (sources : query.sources = [.first position])
    (present : catalog.raw.catalog.tableAt position = some shape)
    (calm : (Resolved.Statement.query query []).Calm) (single : query.compound = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (noOverflow : query.fails (Resolved.EvalContext.bound parameters) (db.scanAt position) = false)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters) (db.scanAt position) = true)
    {property : List (List Value) → Prop}
    (each : ∀ result ∈ query.possibleResults (Resolved.EvalContext.bound parameters) (db.scanAt position),
      property result) :
    (db.run (Belay.Sqlite.query script one) env).returnsResult property := by
  obtain ⟨_, found⟩ := resolve_of_selectQuery (db := catalog) rfl {} resolved
  refine Run.query_returns_catalog_rows head one env schema ?_ sources present calm single limitParameter offsetParameter noOverflow distinct each
  simp [statementOutputAt, found]

#print axioms resolve_of_selectQuery
#print axioms check_query_ofResolveState
#print axioms check_query_ofCatalog
#print axioms query_returnsResult_ofCatalog

end Belay.Sqlite.ReplacedCatalog
