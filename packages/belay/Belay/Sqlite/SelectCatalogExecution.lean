import Belay.Sqlite.SelectCalmExecution
import Belay.Sqlite.ReadAnalysis

set_option doc.verso true

/-! The execution rule of a calm SELECT over one table for every database with a fixed catalog
({name}`Belay.Sqlite.Database.HasCatalog`), and the source rule of the rows that it scans. The
resolution of the statement reads only the catalog, so the rule takes the query to which the statement
resolves on the catalog database; the rows are those of the database, in the order of a full scan
({lit}`Database.scanAt`). The procedure of {lit}`sql_select` starts with this rule. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- The rows of the table at a catalog position, each as its values in column order, in the order of a
full scan; no rows when the position has no table. For example, {lit}`db.scanAt 0` is the rows of the
first table of the catalog. -/
def Database.scanAt (db : Database) (position : Nat) : List (List Value) :=
  ((db.raw.table position).map Resolved.sourceRows).getD []

/-- The query and the subqueries to which a statement resolves on the connection of the database, when
it resolves to a query; {lean}`(none : Option (Resolved.Query × List Resolved.Query))` for a prepare
error or any other statement. The result reads only the catalog of the database. -/
def Database.selectQuery? (db : Database) (statement : Syntax.Statement) :
    Option (Resolved.Query × List Resolved.Query) :=
  match resolveStatement runContext (db.raw.connection {}).resolveState statement with
  | .ok (.query query subqueries, _) => some (query, subqueries)
  | .ok (.createView .., _) | .ok (.createTable .., _) | .ok (.createIndex .., _) | .ok (.createTrigger .., _)
  | .ok (.addColumn .., _) | .ok (.drop .., _) | .ok (.rewrite _, _) | .ok (.dropColumn .., _) | .ok (.begin, _)
  | .ok (.commit, _) | .ok (.rollback, _) | .ok (.insert .., _) | .ok (.update .., _) | .ok (.upsert .., _)
  | .ok (.insertSelect .., _) | .ok (.delete .., _) | .ok (.prepareError _, _) | .ok (.setting .., _)
  | .error _ => none

/-- A calm statement is decided by the check of each of its expressions ({name}`Resolved.Expr.Calm`). -/
instance (statement : Resolved.Statement) : Decidable statement.Calm :=
  inferInstanceAs (Decidable (∀ expression ∈ statement.clockExpressions, expression.Calm))

/-- For every two databases with the same catalog and all counters, the resolution state of the connection
of the first with the counters is that of the connection of the second. Proof sketch: the state reads
only the catalog. -/
theorem Database.resolveState_of_catalog (db catalog : Database) (schema : db.HasCatalog catalog)
    (counters : Counters) : (db.raw.connection counters).resolveState = (catalog.raw.connection {}).resolveState := by
  simp only [Connection.resolveState, Database.Raw.connection]
  rw [show db.raw.catalog = catalog.raw.catalog from schema]

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
gives the results of the query over no rows. Proof sketch: the resolution reads only the catalog
({name}`Database.resolveState_of_catalog`), the catalog gives the table of {lit}`db`, and
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
  obtain ⟨after, resolution⟩ : ∃ after, resolveStatement runContext (db.raw.connection env.counters).resolveState
      statement = .ok (.query query [], after) := by
    rw [Database.resolveState_of_catalog db catalog schema]
    unfold Database.selectQuery? at resolved
    split at resolved
    · cases resolved
      exact ⟨_, ‹_›⟩
    all_goals cases resolved
  have table : db.raw.table position = some { shape, rows := db.raw.rows.getD position [] } := by
    simp [Database.table, show db.raw.catalog = catalog.raw.catalog from schema, present]
  have scan : db.scanAt position = Resolved.sourceRows { shape, rows := db.raw.rows.getD position [] } := by
    simp [Database.scanAt, table]
  rw [scan] at noOverflow distinct each
  exact (Run.query_returnsResult_calmTable head one db env resolution sources table calm single limitParameter
    offsetParameter noOverflow distinct property).mpr each

/-- The cells of a row that NOT NULL columns forbid to be NULL: with one flag for each column, true for
a NOT NULL column, each cell under a true flag is not NULL. Cells past the flags, and flags past the
cells, require nothing. -/
def NotNullCells : List Bool → List Value → Prop
  | true :: flags, value :: values => value ≠ .null ∧ NotNullCells flags values
  | false :: flags, _ :: values => NotNullCells flags values
  | [], _ | _ :: _, [] => True

/-- Source rule of a scan: for every database {lit}`db`, database {lit}`catalog` whose catalog
{lit}`db` has, catalog position with the table {lit}`shape` in the catalog, and scanned row of
{lit}`db` at the position ({name}`Database.scanAt`), the row has one cell for each column of
{lit}`shape`, and no cell of a NOT NULL column is NULL ({name}`NotNullCells`). Proof sketch: the
scanned row is the values of a stored row, which the validity of {lit}`db` makes as wide as the table
and keeps from NULL in a NOT NULL column. -/
theorem Database.mem_scanAt {db catalog : Database} (schema : db.HasCatalog catalog) {position : Nat}
    {shape : CatalogTable} (present : catalog.raw.catalog.tableAt position = some shape) {row : List Value}
    (member : row ∈ db.scanAt position) :
    row.length = shape.columns.length ∧ NotNullCells (shape.columns.map (·.notNull)) row := by
  have table : db.raw.table position = some { shape, rows := db.raw.rows.getD position [] } := by
    simp [Database.table, show db.raw.catalog = catalog.raw.catalog from schema, present]
  simp only [Database.scanAt, table, Option.map_some, Option.getD_some] at member
  obtain ⟨stored, storedIn, rfl⟩ := (mem_sourceRows_iff _ _).mp member
  have wide := db.valid.admitted.rowsWide position _ table stored storedIn
  refine ⟨wide, ?_⟩
  have cells : ∀ (index : Nat) (column : CatalogColumn) (value : Value), shape.columns[index]? = some column →
      stored.values[index]? = some value → column.notNull = true → value ≠ .null := fun index column value =>
    db.notNull position _ table stored storedIn index column value
  clear wide storedIn table
  generalize stored.values = values at cells
  generalize shape.columns = columns at cells
  induction columns generalizing values with
  | nil => simp [NotNullCells]
  | cons column columns step =>
    cases values with
    | nil => cases column.notNull <;> simp [NotNullCells]
    | cons value values =>
      have rest := step values fun index => cells (index + 1)
      cases required : column.notNull
      · simpa [NotNullCells, required] using rest
      · simpa [NotNullCells, required] using And.intro (cells 0 column value rfl rfl required) rest

end Belay.Sqlite
