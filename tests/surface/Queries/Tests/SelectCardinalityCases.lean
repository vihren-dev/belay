import SelectProjectionCases

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A04 of the projection and filter rules of ADR 0027: a plain projection keeps the
number of rows of its table and each duplicate, and a filter bounds the number of rows, each over
every database with generic table and column premises; the contrast shows that a property of each row
gives neither a number of rows nor distinct rows. -/

namespace SelectCardinalityCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectProjectionCases

/-- The query of A04: every customer, with no filter. -/
def customers : Script := sql r"SELECT customer FROM invoices"

/-- The query of A04 has one statement. -/
theorem customers_one : customers.statements.length = 1 := rfl

/-- A04 with generic premises: for every database and environment, when the catalog has a table
{lit}`invoices` at a position with a column {lit}`customer`, the query of every customer returns a
result, and the result is a permutation of the customer cells of the stored rows of the table, one row
for each stored row. So the result has as many rows as the table, and each row occurs as often as
the customer occurs in the table. Proof sketch: the resolution laws give the simple query of the table
without a condition; {name}`Run.query_returnsResult_calmTable` reduces the claim to the possible
results over the scan; {name}`Resolved.Query.perm_of_mem_possibleResults_plain` makes each a
permutation of the outputs of all scanned rows, and the scan is a permutation of the stored rows
({name}`sourceRows_perm`). -/
theorem customers_perm (db : Database) (env : Env) {position customerIndex : Nat} {table : CatalogTable}
    (found : db.raw.catalog.findTable (name! "invoices") = some (position, table))
    (customerFound : columnPosition table.columns (name! "customer") = some customerIndex) :
    (db.run (query customers customers_one) env).returnsResult fun result =>
      result.Perm ((db.raw.rows.getD position []).map fun stored => [stored.values.getD customerIndex .null]) := by
  obtain ⟨names, resolved⟩ := resolveStatement_select_column runContext (db.raw.connection env.counters).resolveState
    { table := name! "invoices", alias := none } none position table none (name! "customer") "customer" rfl rfl rfl
    found customerFound (FilterResolves.of_none _ _ _ _)
  rw [Run.query_returnsResult_calmTable (script := customers) rfl customers_one db env resolved rfl
    (Database.table_of_findTable _ _ _ _ found)
    (Resolved.Statement.simpleColumn_calm _ _ _ _ (by simp)) rfl rfl rfl (by simp [Resolved.Query.fails,
      Resolved.Query.simple]) rfl]
  intro result member
  have perm := Resolved.Query.perm_of_mem_possibleResults_plain rfl rfl rfl rfl rfl member
  rw [Resolved.filtered_of_filter_none _ rfl] at perm
  refine perm.trans (((sourceRows_perm _).map _).trans ?_)
  simp [Function.comp_def, Resolved.Query.rowOutput, Resolved.Query.simple, Resolved.Expr.eval_column,
    List.getD_eq_getElem?_getD]

/-- A04 length: under the premises of {name}`customers_perm`, the query of every customer returns a
result with exactly as many rows as the table has. Proof sketch: a permutation keeps the length
({name}`Run.returnsResult.mono`). -/
theorem customers_length (db : Database) (env : Env) {position customerIndex : Nat} {table : CatalogTable}
    (found : db.raw.catalog.findTable (name! "invoices") = some (position, table))
    (customerFound : columnPosition table.columns (name! "customer") = some customerIndex) :
    (db.run (query customers customers_one) env).returnsResult (·.length = (db.raw.rows.getD position []).length) :=
  (customers_perm db env found customerFound).mono fun _ perm => by simpa using perm.length_eq

/-- The query of the filter bound of A04: the customers of the invoices with a positive amount. -/
def payingCustomers : Script := sql r"SELECT customer FROM invoices WHERE amount > 0"

/-- The filter query has one statement. -/
theorem payingCustomers_one : payingCustomers.statements.length = 1 := rfl

/-- A04 filter bound: for every database and environment, when the catalog has a table
{lit}`invoices` at a position with the columns {lit}`customer` and {lit}`amount`, the query of the
customers with a positive amount returns a result with at most as many rows as the table has. Proof
sketch: as {name}`customers_perm`; the length of a result is at most the number of the query's records
({name}`Resolved.Query.length_le_of_mem_possibleResults`), which are the kept rows, a sublist of the
scan ({name}`Resolved.filtered_sublist`). -/
theorem paying_length_le (db : Database) (env : Env) {position customerIndex amountIndex : Nat}
    {table : CatalogTable}
    (found : db.raw.catalog.findTable (name! "invoices") = some (position, table))
    (customerFound : columnPosition table.columns (name! "customer") = some customerIndex)
    (amountFound : columnPosition table.columns (name! "amount") = some amountIndex) :
    (db.run (query payingCustomers payingCustomers_one) env).returnsResult
      (·.length ≤ (db.raw.rows.getD position []).length) := by
  have resolves := FilterResolves.of_term (dqs := runContext.profile.dqsDml)
    (scope := tableScope db.raw.catalog { table := name! "invoices", alias := none } position table) (aliases := [])
    (shapes := { later := [] })
    (term := .compare .gt (.identifier (name! "amount") .none) (.numeric "0")) (by simp [namesAlias])
    (by simp [resolveOperand_compare_of_notBoolean _ (Syntax.Expr.numeric "0") rfl,
      resolveOperand_identifier_table amountFound, resolveOperand_numeric]; rfl)
  obtain ⟨names, resolved⟩ := resolveStatement_select_column runContext (db.raw.connection env.counters).resolveState
    { table := name! "invoices", alias := none } _ position table _ (name! "customer") "customer" rfl rfl rfl found
    customerFound resolves
  rw [Run.query_returnsResult_calmTable (script := payingCustomers) rfl payingCustomers_one db env resolved rfl
    (Database.table_of_findTable _ _ _ _ found) ?calm rfl rfl rfl ?noOverflow rfl]
  · intro result member
    have bound := Resolved.Query.length_le_of_mem_possibleResults member
    rw [← List.length_map (f := Prod.fst), Resolved.Query.uniqueRecords_outputs_plain _ rfl rfl rfl,
      List.length_map] at bound
    refine Nat.le_trans bound (Nat.le_trans (Resolved.filtered_sublist _ _ _).length_le ?_)
    rw [(sourceRows_perm _).length_eq, List.length_map]
    exact Nat.le_refl _
  · refine Resolved.Statement.simpleColumn_calm _ _ _ _ fun expression member => ?_
    simp only [Option.toList_some, List.mem_singleton] at member
    subst member
    exact (Resolved.Expr.calm_compare ..).mpr ⟨Resolved.Expr.calm_column _, Resolved.Expr.calm_literal _⟩
  · simp [Resolved.Query.fails, Resolved.Query.simple]

/-- Two invoices of the same customer. -/
def repeated : Database := db! r"
  CREATE TABLE invoices (id INTEGER PRIMARY KEY, customer TEXT NOT NULL, amount INTEGER NOT NULL);
  INSERT INTO invoices VALUES (1, 'acme', 10), (2, 'acme', 0);"

/-- A04 witness: on {name}`repeated`, the query of every customer keeps the duplicate customer, and
the filter keeps one of the two rows. -/
theorem duplicate_witness :
    (repeated.run (query customers customers_one)).returnsResult
      (· = [[.text "acme".toUTF8.toList], [.text "acme".toUTF8.toList]]) ∧
      (repeated.run (query payingCustomers payingCustomers_one)).returnsResult (·.length = 1) :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- A04 contrast: a property of each row gives neither a number of rows nor distinct rows. On
{name}`repeated` and on the empty {name}`invoices`, every row of the result of the query of every customer
has a non-NULL first cell; the first result has two equal rows, and the two results have different
lengths. -/
theorem row_property_contrast :
    (repeated.run (query customers customers_one)).returnsRows firstCellPresent ∧
      (repeated.run (query customers customers_one)).returnsResult (fun result => ¬ result.Nodup) ∧
      (invoices.run (query customers customers_one)).returnsRows firstCellPresent ∧
      (invoices.run (query customers customers_one)).returnsResult (·.length = 0) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms customers_perm
#print axioms customers_length
#print axioms paying_length_le
#print axioms duplicate_witness
#print axioms row_property_contrast

end SelectCardinalityCases
