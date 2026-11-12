import SelectProcedureCases

set_option doc.verso true

/-! The core set of the SELECT acceptance cases (A01, A02, A03, A04, A08, A10, A13 and A14), each proved
by {lit}`sql_auto` with the catalog fact as its only hint. The route {lit}`sql_select` closes each claim,
and the info message offers {lit}`sql_select [schema]` as the replacement of the call. The module
{lit}`SelectProcedureCases` proves the same claims with this replacement alone, so the replacement
needs no route search. -/

namespace SelectAutoCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectProjectionCases SelectGroupCases

/-- info: Replace sql_auto with its steps:
  [apply] sql_select [schema] -/
#guard_msgs (whitespace := lax) in
/-- A01: for every database with the catalog of {name}`invoices` and every environment, the motivating
query returns a result, and each of its rows has a first cell that is not NULL
({name}`firstCellPresent`). -/
theorem customer_present (db : Database) (env : Env) (schema : db.HasCatalog invoices) :
    (db.run (query customerOfFirst customerOfFirst_one) env).returnsRows firstCellPresent := by
  sql_auto [schema]

/-- info: Replace sql_auto with its steps:
  [apply] sql_select [schema] -/
#guard_msgs (whitespace := lax) in
/-- A02: for every database with the catalog of {name}`SelectFilterCases.notes`, whose column
{lit}`note` accepts NULL, and every environment, the query of the present notes returns a result, and
each of its rows has a first cell that is not NULL. -/
theorem present_notes (db : Database) (env : Env) (schema : db.HasCatalog SelectFilterCases.notes) :
    (db.run (query SelectFilterCases.presentNotes SelectFilterCases.presentNotes_one) env).returnsRows
      firstCellPresent := by
  sql_auto [schema]

/-- info: Replace sql_auto with its steps:
  [apply] sql_select [schema] -/
#guard_msgs (whitespace := lax) in
/-- A03: for every database with the catalog of {name}`invoices`, every environment and every value
{lit}`minimum`, the query of the amounts above the minimum returns a result, and each of its rows is
one value above the bound minimum ({name}`boundValue`) under the comparison of an INTEGER column with
{lit}`BINARY` ({name}`SelectComparisonCases.aboveMinimum`). -/
theorem amounts_above (db : Database) (env : Env) (minimum : Value) (schema : db.HasCatalog invoices) :
    (db.run (query (SelectComparisonCases.above minimum) (SelectComparisonCases.above_one minimum)) env).returnsRows
      (SelectComparisonCases.aboveMinimum (some .integer) .binary (boundValue minimum)) := by
  sql_auto [schema]

/-- info: Replace sql_auto with its steps:
  [apply] sql_select [schema] -/
#guard_msgs (whitespace := lax) in
/-- A04: for every database with the catalog of {name}`invoices` and every environment, the query of
every customer returns a result that is a permutation of the customer cells of the scanned rows
({name}`Database.scanAt`), one row for each scanned row. -/
theorem customers_perm (db : Database) (env : Env) (schema : db.HasCatalog invoices) :
    (db.run (query SelectCardinalityCases.customers SelectCardinalityCases.customers_one) env).returnsResult
      fun result => result.Perm ((db.scanAt 0).map fun row => [row.getD 1 .null]) := by
  sql_auto [schema]

/-- info: Replace sql_auto with its steps:
  [apply] sql_select [schema] -/
#guard_msgs (whitespace := lax) in
/-- A08: for every database with the catalog of {name}`orders` and every environment, {lit}`count(*)`
returns one row with the number of scanned rows, also 0 for no row. -/
theorem count_rows (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query SelectCountCases.countAll SelectCountCases.countAll_one) env).returnsResult
      (· = [[.integer (db.scanAt 0).length]]) := by
  sql_auto [schema]

/-- info: Replace sql_auto with its steps:
  [apply] sql_select [schema] -/
#guard_msgs (whitespace := lax) in
/-- A10: for every database with the catalog of {name}`orders` and every environment, the query of the
repeat customers returns a result that is a permutation of one row for each group of the scanned rows
by the customer under {lit}`NOCASE` ({name}`Resolved.groups`) that has more than one row: the customer
of the first row of the group and the number of rows. -/
theorem repeat_customers (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query SelectHavingCases.repeatCustomers SelectHavingCases.repeatCustomers_one) env).returnsResult
      fun result => result.Perm (((Resolved.groups (.bound []) [(.column 1, .nocase)] (db.scanAt 0)).filter
        fun group => decide (1 < group.length)).map fun group => [(group.headD []).getD 1 .null, .integer group.length]) := by
  sql_auto [schema]

/-- info: Replace sql_auto with its steps:
  [apply] sql_select [schema] -/
#guard_msgs (whitespace := lax) in
/-- A13: for every database with the catalog of {name}`orders` and every environment, the query of the
ids by descending amount returns the ids of a permutation of the scanned rows in which the amount of
each row is at least the amount of every later row under {lit}`BINARY`. -/
theorem ids_descending (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query SelectOrderCases.idsDescending SelectOrderCases.idsDescending_one) env).returnsResult fun result =>
      ∃ ordered : List (List Value), ordered.Perm (db.scanAt 0) ∧
        ordered.Pairwise (fun a b => (Collation.binary.compare (b.getD 2 .null) (a.getD 2 .null)).isLE) ∧
        result = ordered.map fun row => [row.getD 0 .null] := by
  sql_auto [schema]

/-- info: Replace sql_auto with its steps:
  [apply] sql_select [schema] -/
#guard_msgs (whitespace := lax) in
/-- A14: for every database with the catalog of {name}`orders` and every environment, the query of the
window {lit}`LIMIT 2 OFFSET 1` returns a result such that:

* it has the smaller of 2 and the number of scanned rows less one rows;
* it is the ids of a permutation of a sublist of the scanned rows in which the amount of each row is at
  most the amount of every later row under {lit}`BINARY`. -/
theorem ids_window (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query SelectOrderCases.idsWindow SelectOrderCases.idsWindow_one) env).returnsResult fun result =>
      result.length = min 2 ((db.scanAt 0).length - 1) ∧
      ∃ picked : List (List Value), (∃ chosen, chosen.Sublist (db.scanAt 0) ∧ picked.Perm chosen) ∧
        picked.Pairwise (fun a b => (Collation.binary.compare (a.getD 2 .null) (b.getD 2 .null)).isLE) ∧
        result = picked.map fun row => [row.getD 0 .null] := by
  sql_auto [schema]

end SelectAutoCases

#print axioms SelectAutoCases.customer_present
#print axioms SelectAutoCases.present_notes
#print axioms SelectAutoCases.amounts_above
#print axioms SelectAutoCases.customers_perm
#print axioms SelectAutoCases.count_rows
#print axioms SelectAutoCases.repeat_customers
#print axioms SelectAutoCases.ids_descending
#print axioms SelectAutoCases.ids_window
