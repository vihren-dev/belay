import Belay

set_option doc.verso true
set_option sql.check false

/-! A write can have the same output as a table scan without resolving to a query. -/

namespace CatalogOutputCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- An empty table for both the write and the comparison scan. -/
def emptyTable : Database := db! r"CREATE TABLE t (a)"

/-- The UPDATE returns one row for each updated row. -/
def updateRows : Script := sql r"UPDATE t SET a = 7 RETURNING a"

/-- A scan that returns the first column of each row. -/
def scan : Resolved.Query := Resolved.Query.simple [.first 0] none [.scalar (.column 0)] ["a"]

/-- The UPDATE on the empty table resolves to a nonquery and returns no rows. Proof sketch:
compute the catalog lookup and output equality, then apply {name}`Run.query_returns_catalog_rows` to the empty scan. -/
theorem update_returns_empty :
    emptyTable.selectQuery? updateRows.statements[0].1 = none ∧
    (emptyTable.run (query updateRows rfl)).returnsResult (· = []) := by
  refine ⟨by decide +kernel, ?_⟩
  let shape := ((emptyTable.raw.catalog.findTable (name! "t")).get (by decide +kernel)).2
  refine Run.query_returns_catalog_rows (script := updateRows) rfl rfl Env.default
    (catalog := emptyTable) rfl (query := scan) (position := 0) (shape := shape)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) rfl rfl rfl
    (by decide +kernel) (by decide +kernel) ?_
  intro rows member
  have perm := Resolved.Query.perm_of_mem_possibleResults_plain rfl rfl rfl rfl rfl member
  change rows.Perm [] at perm
  exact List.perm_nil.mp perm

/-- At the concrete empty database and default environment, {name}`Select.closeByEvaluation` infers
the query in the {name}`statementOutputAt` equation used by {name}`Run.query_returns_catalog_rows`. -/
theorem select_returns_empty :
    (emptyTable.run (query (sql r"SELECT a FROM t") rfl)).returnsResult (fun rows => rows = []) := by
  have empty : emptyTable.scanAt 0 = [] := by decide +kernel
  sql_select [empty]

/-- With all counters initially zero, the empty UPDATE also keeps the full connection.
For every clock, statement index and parameter list this write realizes the certified
scan. The lookup identifies the concrete empty table, and both steps compute. -/
theorem empty_write_realizes_scan :
    (⟨0, 1, none, [.scalar (.column 0)]⟩ : ReadCertificate).Scans runContext updateRows.statements[0].1
      (emptyTable.raw.connection Counters.newConnection) := by
  refine ⟨["a"], ?_⟩
  intro clock index parameters table present
  let actual := (emptyTable.raw.table 0).get (by decide +kernel)
  have located : (emptyTable.raw.connection Counters.newConnection).state.database.table 0 = some actual := by
    decide +kernel
  change (emptyTable.raw.connection Counters.newConnection).state.database.table 0 = some table at present
  rw [located] at present
  rw [← Option.some.inj present]
  rfl

#print axioms empty_write_realizes_scan
#print axioms select_returns_empty
#print axioms update_returns_empty

end CatalogOutputCases
