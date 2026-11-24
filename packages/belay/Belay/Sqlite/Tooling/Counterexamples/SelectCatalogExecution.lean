import Belay.Sqlite.Tooling.Counterexamples.SelectCalmExecution
import Belay.Sqlite.Programs.StatementRunLaws.SelectCatalogExecution
import Belay.Sqlite.Schema.Dispatch.SelectCatalogExecution

set_option doc.verso true

/-! The execution rule of a calm SELECT over one table for every database with a fixed catalog
({name}`Belay.Sqlite.Database.HasCatalog`), and the source rule of the rows that it scans. The
resolution of the statement reads only the catalog, so the rule takes an equation for the output computed
with that catalog on the runtime connection; the rows are those of the database, in the order of a full scan
({lit}`Database.scanAt`). The procedure of {lit}`sql_select` starts with this rule. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- At any clock, index and connection with a table at the given position, the output of a calm
one-table query returns rows with a property exactly when every possible result of its scan has
that property. The source is the first table, the query is simple, the window binds without
parameters, and the scan rules out overflow and uncertain DISTINCT. Proof sketch:
{name}`Connection.SelectReady.of_faultless` supplies readiness and {name}`resolvedStepOutput_select`
evaluates the output in the context of the bound parameter values. -/
theorem resolvedStepOutput_calm_scan (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) {query : Resolved.Query} {position : Nat} {table : Table}
    (sources : query.sources = [.first position]) (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query query []).Calm) (single : query.compound = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (noOverflow : query.fails (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = false)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = true)
    (property : List (List Value) → Prop) :
    (resolvedStepOutput clock index connection parameters (.query query [])).returnsResult property ↔
      ∀ rows ∈ query.possibleResults (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table),
        property rows := by
  have faultless := calm.faultless_nil connection parameters (rows := Resolved.sourceRows table)
  rw [Connection.queryContext_calm _ parameters query [] calm] at faultless
  have ready := Connection.SelectReady.of_faultless connection parameters calm single
    (Resolved.Query.bindWindow_literal parameters query limitParameter offsetParameter)
    (Resolved.Query.source_first _ query connection.state.database position _ sources present) (by simp)
    faultless noOverflow distinct
  rw [resolvedStepOutput_select clock index connection parameters (by simp [statementClock, calm.readsClock]) ready,
    show connection.queryContextAt 0 parameters query [] = Resolved.EvalContext.bound parameters
      from Connection.queryContext_of_quiet _ _ _ calm.quiet]
  exact query.returnsResult_possible _ _ property

/-- Catalog rule: for every script of one statement with its values, proof that it has one statement,
database {lit}`db`, environment, database {lit}`catalog` whose catalog {lit}`db` has, query, catalog
position, catalog table {lit}`shape` and property {lit}`Q` of a result, the run of the program
{name}`query` of the script on {lit}`db` returns a result with {lit}`Q` when:
* the output computed with {name}`statementOutputAt` on the fixed catalog equals the output of the
  query with no subqueries, both evaluated on the runtime connection;
* the query reads only the table at the position, which is {lit}`shape` in the catalog;
* the query is calm ({name}`Resolved.Statement.Calm`), no compound, and binds no {lit}`LIMIT` or
  {lit}`OFFSET` parameter;
* over the scanned rows of the table in {lit}`db` ({name}`Database.scanAt`), with the values of the
  statement, the query has no overflow ({lit}`Query.fails`) and a certain {lit}`DISTINCT`;
* every result that the model permits for the query over these rows has {lit}`Q`.

The clock and the counters of the environment do not matter. The rule requires no row: an empty table
gives the results of the query over no rows. Proof sketch: {name}`runScriptStep_output_at` transports the output, {name}`Database.table_of_catalog`
gives the runtime scan, and {name}`resolvedStepOutput_select` gives its possible results. -/
theorem Run.query_returns_catalog_rows {script : Script} {statement : Syntax.Statement} {parameters : List Value}
    (head : script.statements = [(statement, parameters)]) (one : script.statements.length = 1) {db : Database}
    (env : Env) {catalog : Database} (schema : db.HasCatalog catalog) {query : Resolved.Query} {position : Nat}
    {shape : CatalogTable}
    (observed : statementOutputAt runContext (catalog.raw.connection {}).resolveState statement
      env.clock 0 (db.raw.connection env.counters) parameters =
      resolvedStepOutput env.clock 0 (db.raw.connection env.counters) parameters (.query query []))
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
  obtain ⟨table, scan⟩ := Database.table_of_catalog schema present
  rw [scan] at noOverflow distinct each
  rw [Run.query_returnsResult_iff one]
  have entry : script.statements[0]'(by rw [one]; decide) = (statement, parameters) := by simp [head]
  rw [entry, runScriptStep_output_at (Database.resolveState_of_catalog db catalog schema env.counters), observed]
  exact (resolvedStepOutput_calm_scan _ _ _ _ sources table calm single limitParameter offsetParameter
    noOverflow distinct property).2 each

end Belay.Sqlite
