import Belay.Sqlite.Tooling.Counterexamples.SelectCalmExecution
import Belay.Sqlite.Programs.StatementRunLaws.SelectCatalogExecution
import Belay.Sqlite.Schema.Dispatch.SelectCatalogExecution

set_option doc.verso true

/-! The execution rule of a calm SELECT over one table for every database with a fixed catalog
({name}`Belay.Sqlite.Database.HasCatalog`), and the source rule of the rows that it scans. The
resolution of the statement reads only the catalog, so the rule takes the query to which the statement
resolves on the catalog database; the rows are those of the database, in the order of a full scan
({lit}`Database.scanAt`). The procedure of {lit}`sql_select` starts with this rule. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- Catalog rule: for every script of one statement with its values, proof that it has one statement,
database {lit}`db`, environment, database {lit}`catalog` whose catalog {lit}`db` has, query, catalog
position, catalog table {lit}`shape` and property {lit}`Q` of a result, the run of the program
{name}`query` of the script on {lit}`db` returns a result with {lit}`Q` when:
* the statement resolves on {lit}`catalog` to the query with no subqueries
  ({name}`Database.selectQuery?`);
* the query reads only the table at the position, which is {lit}`shape` in the catalog;
* the query is calm ({name}`Resolved.Statement.Calm`), no compound, and binds no {lit}`LIMIT` or
  {lit}`OFFSET` parameter;
* over the scanned rows of the table in {lit}`db` ({name}`Database.scanAt`), with the values of the
  statement, the query has no overflow ({lit}`Query.fails`) and a certain {lit}`DISTINCT`;
* every result that the model permits for the query over these rows has {lit}`Q`.

The clock and the counters of the environment do not matter. The rule requires no row: an empty table
gives the results of the query over no rows. Proof sketch: {name}`Database.resolve_of_selectQuery`
and {name}`Database.table_of_catalog` give the resolution and the table of {lit}`db`, and
{name}`Run.query_returnsResult_calmTable` gives the result. -/
theorem Run.query_returnsResult_ofCatalog {script : Script} {statement : Syntax.Statement} {parameters : List Value}
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
  obtain ⟨after, resolution⟩ := Database.resolve_of_selectQuery schema env.counters resolved
  obtain ⟨table, scan⟩ := Database.table_of_catalog schema present
  rw [scan] at noOverflow distinct each
  exact (Run.query_returnsResult_calmTable head one db env resolution sources table calm single limitParameter
    offsetParameter noOverflow distinct property).mpr each

end Belay.Sqlite
