import Belay

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance cases of the projection and filter rules of ADR 0027: A01, the motivating query
{lit}`SELECT customer FROM invoices WHERE id=1` over every database, once with generic table and
column premises and once with the catalog fact {lit}`db.HasCatalog invoices`, with an empty and a
populated witness and the nullable contrast. -/

namespace SelectProjectionCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The motivating query of ADR 0027: the customer of invoice 1. -/
def customerOfFirst : Script := sql r"SELECT customer FROM invoices WHERE id=1"

/-- The motivating query has one statement. -/
theorem customerOfFirst_one : customerOfFirst.statements.length = 1 := rfl

/-- A row has a first cell, and it is not NULL. -/
def firstCellPresent (row : List Value) : Prop := ∃ value, row.head? = some value ∧ value ≠ .null

/-- {name}`firstCellPresent` is decided by the first cell. -/
instance : DecidablePred firstCellPresent := fun row =>
  match row with
  | [] => isFalse (by simp [firstCellPresent])
  | value :: _ => decidable_of_iff (value ≠ .null) (by simp [firstCellPresent])

/-- A01 with generic premises: for every database and environment, when the catalog has a table
{lit}`invoices` at a position with a column {lit}`id` and a NOT NULL column {lit}`customer`, the
motivating query returns a result, and each of its rows has a first cell that is not NULL. The
table can have other columns in any order, and any rows, also none: an empty result satisfies the
claim. Proof sketch: the resolution laws give the simple query of the table;
{name}`Run.query_returnsResult_calmTable` reduces the claim to the possible results over the
scan; {name}`Resolved.Query.mem_possibleResults_plain` traces each row to a stored row, whose
cell the validity of the database ({name}`Database.notNull`) keeps non-NULL. -/
theorem customer_present_of_columns (db : Database) (env : Env) {position idIndex customerIndex : Nat}
    {table : CatalogTable} {customer : CatalogColumn}
    (found : db.raw.catalog.findTable (name! "invoices") = some (position, table))
    (idFound : columnPosition table.columns (name! "id") = some idIndex)
    (customerFound : columnPosition table.columns (name! "customer") = some customerIndex)
    (customerAt : table.columns[customerIndex]? = some customer) (required : customer.notNull = true) :
    (db.run (query customerOfFirst customerOfFirst_one) env).returnsRows
      firstCellPresent := by
  have resolves := FilterResolves.of_term (dqs := runContext.profile.dqsDml)
    (scope := tableScope db.raw.catalog { table := name! "invoices", alias := none } position table) (aliases := [])
    (shapes := { later := [] })
    (term := .compare .eq (.identifier (name! "id") .none) (.numeric "1")) (by simp [namesAlias])
    (by simp [sql_simp, idFound]; rfl)
  obtain ⟨names, resolved⟩ := resolveStatement_select_column runContext (db.raw.connection env.counters).resolveState
    { table := name! "invoices", alias := none } _ position table _ (name! "customer") "customer" rfl rfl rfl found
    customerFound resolves
  rw [Run.returnsRows, Run.query_returnsResult_calmTable (script := customerOfFirst) rfl customerOfFirst_one db env resolved rfl
    (Database.table_of_findTable _ _ _ _ found) ?calm rfl rfl rfl ?noOverflow rfl]
  · intro result member row inResult
    obtain ⟨source, inSource, -, rfl⟩ := Resolved.Query.mem_possibleResults_plain rfl rfl rfl member inResult
    have present := Database.table_of_findTable _ _ _ _ found
    obtain ⟨stored, storedIn, rfl⟩ := (mem_sourceRows_iff _ source).mp inSource
    have wide := db.valid.admitted.rowsWide position _ present stored storedIn
    have inside : customerIndex < stored.values.length := wide ▸ (List.getElem?_eq_some_iff.mp customerAt).1
    refine ⟨stored.values[customerIndex], ?_, db.notNull position _ present stored storedIn customerIndex customer _
      customerAt (List.getElem?_eq_getElem inside) required⟩
    simp [Resolved.Query.rowOutput, Resolved.Query.simple, Resolved.Expr.eval_column, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem inside]
  · refine Resolved.Statement.simpleColumn_calm _ _ _ _ fun expression member => ?_
    simp only [Option.toList_some, List.mem_singleton] at member
    subst member
    exact (Resolved.Expr.calm_compare ..).mpr ⟨Resolved.Expr.calm_column _, Resolved.Expr.calm_literal _⟩
  · simp [Resolved.Query.fails, Resolved.Query.simple]

/-- The guide's invoices schema, with no rows. -/
def invoices : Database := db! r"
  CREATE TABLE invoices (
    id INTEGER PRIMARY KEY,
    customer TEXT NOT NULL,
    amount INTEGER NOT NULL CHECK (amount >= 0),
    status TEXT NOT NULL DEFAULT 'open'
  );"

/-- The invoices schema with two invoices. -/
def shop : Database := db! r"
  CREATE TABLE invoices (
    id INTEGER PRIMARY KEY,
    customer TEXT NOT NULL,
    amount INTEGER NOT NULL CHECK (amount >= 0),
    status TEXT NOT NULL DEFAULT 'open'
  );
  INSERT INTO invoices (id, customer, amount) VALUES (1, 'acme', 10), (2, 'zeta', 0);"

/-- The catalog position and the table of {lit}`invoices` in {name}`invoices`. -/
def invoicesTable : Nat × CatalogTable := (invoices.raw.catalog.findTable (name! "invoices")).get (by decide +kernel)

/-- The column {lit}`customer` of {name}`invoicesTable`. -/
def customerColumn : CatalogColumn := invoicesTable.2.columns[1]'(by decide +kernel)

/-- A01 with the catalog fact: for every database with the catalog of {name}`invoices`
({name}`Database.HasCatalog`) and every environment, the motivating query returns a result, and
each of its rows has a first cell that is not NULL. The theorem does not assume that invoice 1
exists, that the cell is TEXT, or that the rows are those of an example. Proof sketch:
{name}`customer_present_of_columns`, whose premises the catalog decides. -/
theorem customer_present (db : Database) (env : Env) (schema : db.HasCatalog invoices) :
    (db.run (query customerOfFirst customerOfFirst_one) env).returnsRows firstCellPresent :=
  customer_present_of_columns db env (position := invoicesTable.1) (idIndex := 0) (customerIndex := 1)
    (table := invoicesTable.2)
    (customer := customerColumn) (by rw [show db.raw.catalog = invoices.raw.catalog from schema]; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- A01 as a {name}`Sql.check` claim at the initial context: for every database with the catalog of
{name}`invoices` and every environment, the program {name}`query` of the motivating query gives a
successful result whose rows each have a non-NULL first cell. Proof sketch: the successful-result
bridge {name}`Run.returnsResult_query_iff` of {name}`customer_present`. -/
theorem customer_present_check (db : Database) (env : Env) (schema : db.HasCatalog invoices) :
    (query customerOfFirst customerOfFirst_one).check (fun result _ => match result with
      | .ok rows => ∀ row ∈ rows, firstCellPresent row | .error _ => False) (ExecutionContext.initial db env) :=
  (Run.returnsResult_query_iff rfl db env _).mp (customer_present db env schema)

/-- The empty witness: {name}`invoices` has its own catalog, and the query returns an empty result
there, which the claim allows. -/
theorem empty_witness :
    invoices.HasCatalog invoices ∧ (invoices.run (query customerOfFirst customerOfFirst_one)).returnsResult (· = []) :=
  ⟨rfl, by decide +kernel⟩

/-- The populated witness: {name}`shop` has the catalog of {name}`invoices`, and the query returns
one row, which has a non-NULL first cell. -/
theorem populated_witness :
    shop.HasCatalog invoices ∧
      (shop.run (query customerOfFirst customerOfFirst_one)).returnsResult (·.length = 1) ∧
      (shop.run (query customerOfFirst customerOfFirst_one)).returnsRows firstCellPresent :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- A table {lit}`invoices` whose column {lit}`customer` accepts NULL, with a NULL customer for
invoice 1. -/
def nullable : Database := db! r"
  CREATE TABLE invoices (id INTEGER PRIMARY KEY, customer TEXT);
  INSERT INTO invoices VALUES (1, NULL);"

/-- A01 contrast: a nullable column cannot establish the claim. On {name}`nullable` the column is
not NOT NULL, and the query returns a row whose first cell is NULL. -/
theorem nullable_contrast :
    ((nullable.raw.catalog.findTable (name! "invoices")).get (by decide +kernel)).2.columns[1]?.map
        CatalogColumn.notNull = some false ∧
      ¬ (nullable.run (query customerOfFirst customerOfFirst_one)).returnsRows firstCellPresent :=
  ⟨by decide +kernel, by decide +kernel⟩

#print axioms customer_present_of_columns
#print axioms customer_present
#print axioms customer_present_check
#print axioms empty_witness
#print axioms populated_witness
#print axioms nullable_contrast

end SelectProjectionCases
