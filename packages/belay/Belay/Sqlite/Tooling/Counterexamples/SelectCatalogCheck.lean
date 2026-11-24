import Belay.Sqlite.Tooling.Counterexamples.SelectCatalogExecution
import Belay.Sqlite.Tooling.Counterexamples.SelectContextExecution

set_option doc.verso true

/-! The rules of a calm SELECT over one table in a check ({lit}`Sql.check`): at any context whose
connection has the resolution state of a fixed catalog, for example the context that a write reached, and
at a context whose connection is that of a database with the catalog
({name}`Belay.Sqlite.Database.HasCatalog`). The second is the rule of
{lit}`Run.query_returns_catalog_rows` for a check: {lit}`sql_run` gives the check of a SELECT in a
program to the procedure of {lit}`sql_select`, which starts with these rules. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- Context catalog check rule: for every script of one SELECT ({name}`Script.isSelect`) with its values,
proof that it has one statement, context {lit}`state`, database {lit}`catalog` such that the connection of
{lit}`state` has the resolution state of a new connection to {lit}`catalog` (its catalog, no open
transaction, and the settings of a new connection), query, catalog position, catalog table {lit}`shape`
and post {lit}`P`, the program {name}`query` of the script checks {lit}`P` at {lit}`state` when:
* the output computed with {name}`statementOutputAt` on the fixed catalog equals the output of the
  query with no subqueries, both evaluated on the runtime connection;
* the query reads only the table at the position, which is {lit}`shape` in the catalog;
* the query is calm ({name}`Resolved.Statement.Calm`), no compound, and binds no {lit}`LIMIT` or
  {lit}`OFFSET` parameter;
* over the source rows of the table in the database of {lit}`state`, with the values of the statement,
  the query has no overflow ({lit}`Query.fails`) and a certain {lit}`DISTINCT`;
* for every result that the model permits for the query over these rows, {lit}`P` holds for the
  result and every context whose connection is the connection of {lit}`state`.

The state can be any context, for example the context that a write reached; the clock, the statement
index, the counters and the outputs of {lit}`state` do not matter. Proof sketch: {name}`runScriptStep_output_at` transfers the output equation to {lit}`state`, whose
database has the catalog of {lit}`catalog` and so the table; calm expressions have no fault
({name}`Resolved.Statement.Calm.faultless_nil`), and {name}`Sql.check_query_of_step_rows` gives the
check. -/
theorem Sql.check_query_catalog_rows_at {script : Script} {one : script.statements.length = 1}
    {statement : Syntax.Statement} {parameters : List Value} (select : script.isSelect = true)
    (head : script.statements = [(statement, parameters)]) {state : ExecutionContext} {catalog : Database}
    (connection : state.connection.resolveState = (catalog.raw.connection {}).resolveState)
    {query : Resolved.Query} {position : Nat} {shape : CatalogTable}
    (observed : statementOutputAt runContext (catalog.raw.connection {}).resolveState statement
      state.clock state.index state.connection parameters =
      resolvedStepOutput state.clock state.index state.connection parameters (.query query []))
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
  have catalogs : state.connection.state.database.catalog = catalog.raw.catalog :=
    congrArg ResolveState.catalog connection
  have table : state.connection.state.database.table position =
      some { shape, rows := state.connection.state.database.rows.getD position [] } := by
    simp [Model.Database.table, catalogs, present]
  refine Sql.check_query_of_step_rows select head state ?_ each
  rw [runScriptStep_output_at connection, observed]
  exact (resolvedStepOutput_calm_scan _ _ _ _ sources table calm single limitParameter offsetParameter
    noOverflow distinct _).2 fun _ member => member

/-- Catalog check rule: for every script of one SELECT ({name}`Script.isSelect`) with its values, proof
that it has one statement, context {lit}`state`, database {lit}`db` with counters such that the
connection of {lit}`state` is the connection of {lit}`db` with the counters, database {lit}`catalog`
whose catalog {lit}`db` has, query, catalog position, catalog table {lit}`shape` and post {lit}`P`, the
program {name}`query` of the script checks {lit}`P` at {lit}`state` when:
* the output computed with {name}`statementOutputAt` on the fixed catalog equals the output of the
  query with no subqueries, both evaluated on the runtime connection;
* the query reads only the table at the position, which is {lit}`shape` in the catalog;
* the query is calm ({name}`Resolved.Statement.Calm`), no compound, and binds no {lit}`LIMIT` or
  {lit}`OFFSET` parameter;
* over the scanned rows of the table in {lit}`db` ({name}`Database.scanAt`), with the values of the
  statement, the query has no overflow ({lit}`Query.fails`) and a certain {lit}`DISTINCT`;
* for every result that the model permits for the query over these rows, {lit}`P` holds for the
  result and every context whose connection is the connection of {lit}`state`.

The clock, the statement index and the outputs of {lit}`state` do not matter. Proof sketch: the
connection of {lit}`db` has the resolution state of {lit}`catalog`
({name}`Database.resolveState_of_catalog`), and its scan is the source rows of the table
({name}`Database.table_of_catalog`), so {name}`Sql.check_query_catalog_rows_at` applies. -/
theorem Sql.check_query_catalog_rows {script : Script} {one : script.statements.length = 1}
    {statement : Syntax.Statement} {parameters : List Value} (select : script.isSelect = true)
    (head : script.statements = [(statement, parameters)]) {state : ExecutionContext} {db : Database}
    {counters : Counters} (connected : state.connection = db.raw.connection counters) {catalog : Database}
    (schema : db.HasCatalog catalog) {query : Resolved.Query} {position : Nat} {shape : CatalogTable}
    (observed : statementOutputAt runContext (catalog.raw.connection {}).resolveState statement
      state.clock state.index state.connection parameters =
      resolvedStepOutput state.clock state.index state.connection parameters (.query query []))
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
  obtain ⟨_, scan⟩ := Database.table_of_catalog schema present
  rw [scan] at noOverflow distinct each
  have database : state.connection.state.database = db.raw := by rw [connected]; rfl
  refine Sql.check_query_catalog_rows_at select head ?_ observed sources present calm single limitParameter
    offsetParameter ?_ ?_ ?_
  · rw [connected]
    exact Database.resolveState_of_catalog db catalog schema counters
  all_goals rw [database]; assumption

end Belay.Sqlite
