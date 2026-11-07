import SelectCountCases

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A09 for {lit}`min` and {lit}`group_concat` (ADR 0027), over every database with
the catalog of {lit}`orders`: {lit}`min(amount)` is NULL exactly for a table without a row, and
otherwise the amount of a stored row that is at most every amount under the modeled comparison of
the column's collation; {lit}`group_concat(customer)` joins the customers in scan order with commas,
through its generic rule. Contrast: in a grouped query a {lit}`min` call decides the row of the
group from which the other columns read ({lit}`Query.deciding`). -/

namespace SelectExtremumCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases SelectCountCases

/-- For every database with the catalog of {name}`orders`, the columns {lit}`customer` (1) and
{lit}`amount` (2) are not NULL on any row of the scan. Proof sketch: each scan row is a stored row
({name}`mem_sourceRows_iff`) as wide as the table, and the validity of the database
({name}`Database.notNull`) gives the NOT NULL cells. -/
theorem ordersRows_notNull (db : Database) (schema : db.HasCatalog orders) {index : Nat} (column : index = 1 ∨ index = 2) :
    ∀ row ∈ ordersRows db, (cell index row).isNull = false := by
  have bound : index < ordersShape.columns.length := by rcases column with rfl | rfl <;> decide +kernel
  have constrained : ∀ inside : index < ordersShape.columns.length, (ordersShape.columns[index]'inside).notNull = true := by
    rcases column with rfl | rfl <;> decide +kernel
  have present := Database.table_of_findTable db.raw _ _ _ (orders_found db schema)
  intro row inRows
  obtain ⟨stored, storedIn, rfl⟩ := (mem_sourceRows_iff _ row).mp inRows
  have wide := db.valid.admitted.rowsWide 0 _ present stored storedIn
  have inside : index < stored.values.length := wide ▸ bound
  have notNull := db.notNull 0 _ present stored storedIn index (ordersShape.columns[index]'bound) _
    (by simp) (List.getElem?_eq_getElem inside) (constrained bound)
  simp [Resolved.Expr.eval_column, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Value.isNull]
  cases h : stored.values[index] <;> simp_all

/-- The A09 query of the least amount. -/
def minAmount : Script := sql r"SELECT min(amount) FROM orders"

/-- The query of the least amount has one statement. -/
theorem minAmount_one : minAmount.statements.length = 1 := rfl

/-- The query to which {name}`minAmount` resolves: {name}`ungroupedQuery` of the {lit}`min` call,
which is also the call that decides the row of the group. -/
def minQuery : Resolved.Query :=
  { ungroupedQuery [.aggregate (.min (.column 2) .binary)] ["min(amount)"] with deciding := some (.min (.column 2) .binary) }

/-- A09 for {lit}`min`: for every database with the catalog of {name}`orders` and every environment,
{name}`minAmount` returns one row of one value {lit}`least`, where

* {lit}`least` is NULL exactly when the table has no row, and
* when the table has a row, {lit}`least` is the amount of a row of the scan, and it is at most the
  amount of every row under the comparison of {lit}`BINARY`, the collation of the column.

Proof sketch: for the catalog the statement resolves to {name}`ungroupedQuery` of {lit}`min`;
{name}`Run.query_returnsResult_calmTable` and {name}`result_ungrouped` give the one row, and the
extremum rule ({name}`Resolved.extremum_spec`) with {name}`ordersRows_notNull` its value. -/
theorem min_amount (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query minAmount minAmount_one) env).returnsResult fun result => ∃ least, result = [[least]] ∧
      (least = .null ↔ ordersRows db = []) ∧
      (ordersRows db ≠ [] → (∃ row ∈ ordersRows db, cell 2 row = least) ∧
        ∀ row ∈ ordersRows db, (Collation.binary.compare least (cell 2 row)).isLE) := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (match minAmount.statements with | (statement, _) :: _ => statement | [] => .begin) =
      .ok (.query minQuery [], (db.raw.connection env.counters).resolveState) := by
    rw [orders_state db env schema]
    decide +kernel
  rw [Run.query_returnsResult_calmTable (script := minAmount) rfl minAmount_one db env resolved rfl
    (Database.table_of_findTable db.raw _ _ _ (orders_found db schema)) (by unfold Resolved.Statement.Calm; decide)
    rfl rfl rfl (by simp [Resolved.Query.fails, minQuery, ungroupedQuery, Resolved.Aggregate.fails]) rfl]
  intro result member
  rw [result_ungrouped rfl rfl rfl rfl rfl rfl rfl rfl member]
  have notNull := ordersRows_notNull db schema (index := 2) (.inr rfl)
  change ∃ least, [(minQuery.groupRecord (Resolved.EvalContext.bound []) (ordersRows db)).1] = [[least]] ∧ _
  generalize ordersRows db = rows at notNull ⊢
  obtain ⟨nullIff, spec⟩ := Resolved.extremum_spec (cmp := Collation.binary.compare) (rows.map (cell 2))
  refine ⟨Resolved.extremum (fun a b => Collation.binary.compare a b == .lt) (rows.map (cell 2)),
    by simp [Resolved.Query.groupRecord, minQuery, ungroupedQuery, Resolved.Aggregate.eval], ⟨fun null => ?_, ?_⟩,
    fun nonempty => ?_⟩
  · cases rows with
    | nil => rfl
    | cons row rest =>
      exact absurd ((nullIff.mp (by rw [null]; rfl)) _ (List.mem_map_of_mem (List.mem_cons_self ..)))
        (by simp [notNull row (List.mem_cons_self ..)])
  · rintro rfl; rfl
  · have present : (Resolved.extremum (fun a b => Collation.binary.compare a b == .lt) (rows.map (cell 2))).isNull =
        false := by
      obtain ⟨row, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
      cases null : (Resolved.extremum (fun a b => Collation.binary.compare a b == .lt) ((row :: rest).map (cell 2))).isNull
      · rfl
      · exact absurd (nullIff.mp null _ (List.mem_map_of_mem (List.mem_cons_self ..)))
          (by simp [notNull row (List.mem_cons_self ..)])
    obtain ⟨found, least⟩ := spec present
    obtain ⟨row, inRows, same⟩ := List.mem_map.mp found
    exact ⟨⟨row, inRows, same⟩, fun other inRows => least _ (List.mem_map_of_mem inRows) (notNull other inRows)⟩

/-- The A09 query of the customers of the orders, joined with commas. -/
def joinedCustomers : Script := sql r"SELECT group_concat(customer) FROM orders"

/-- The query of the joined customers has one statement. -/
theorem joinedCustomers_one : joinedCustomers.statements.length = 1 := rfl

/-- A09 for {lit}`group_concat`: for every database with the catalog of {name}`orders` and every
environment, {name}`joinedCustomers` returns one row of one value:

* NULL when the table has no row;
* when the scan is a first row and later rows, the TEXT of the first row's customer
  ({name}`Resolved.concatText`) followed, for each later row in scan order, by a comma (byte 44) and the
  row's customer.

Proof sketch: as {name}`min_amount`; {name}`Resolved.Aggregate.eval_groupConcat_of_notNull` with
{name}`ordersRows_notNull` gives the text, and the aggregate over no row is NULL. -/
theorem joined_customers (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query joinedCustomers joinedCustomers_one) env).returnsResult fun result =>
      match ordersRows db with
      | [] => result = [[.null]]
      | first :: rest =>
        result = [[.text (Resolved.concatText (cell 1 first) ++ (rest.map fun row => 44 :: Resolved.concatText (cell 1 row)).flatten)]] := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (match joinedCustomers.statements with | (statement, _) :: _ => statement | [] => .begin) =
      .ok (.query (ungroupedQuery [.aggregate (.groupConcat (.column 1) none)] ["group_concat(customer)"]) [],
        (db.raw.connection env.counters).resolveState) := by
    rw [orders_state db env schema]
    decide +kernel
  rw [Run.query_returnsResult_calmTable (script := joinedCustomers) rfl joinedCustomers_one db env resolved rfl
    (Database.table_of_findTable db.raw _ _ _ (orders_found db schema)) (by unfold Resolved.Statement.Calm; decide)
    rfl rfl rfl (by simp [Resolved.Query.fails, ungroupedQuery, Resolved.Aggregate.fails]) rfl]
  intro result member
  rw [result_ungrouped rfl rfl rfl rfl rfl rfl rfl rfl member]
  have notNull := ordersRows_notNull db schema (index := 1) (.inl rfl)
  change match ordersRows db with
    | [] => [((ungroupedQuery [.aggregate (.groupConcat (.column 1) none)] ["group_concat(customer)"]).groupRecord
        (Resolved.EvalContext.bound []) (ordersRows db)).1] = [[.null]]
    | first :: rest => [((ungroupedQuery [.aggregate (.groupConcat (.column 1) none)] ["group_concat(customer)"]).groupRecord
        (Resolved.EvalContext.bound []) (ordersRows db)).1] = _
  generalize ordersRows db = rows at notNull ⊢
  cases rows with
  | nil => rfl
  | cons first rest =>
    simp [Resolved.Query.groupRecord, ungroupedQuery,
      Resolved.Aggregate.eval_groupConcat_of_notNull _ _ first rest notNull]

/-- The grouped query whose {lit}`min` call decides the row of each group. -/
def minByCustomer : Script := sql r"SELECT customer, min(amount) FROM orders GROUP BY customer"

/-- The grouped query of the least amounts has one statement. -/
theorem minByCustomer_one : minByCustomer.statements.length = 1 := rfl

/-- A09 contrast: in a grouped query a {lit}`min` call decides the row of the group from which the
other columns read. On {name}`mixed` the group of {lit}`acme` reads {lit}`'ACME'` from the row of
the least amount, 5, where the grouped count of {name}`counts_witness` reads {lit}`'acme'` from the
first row. Native SQLite 3.51.0 gives the same rows over a scan and over an index on
{lit}`customer`. -/
theorem deciding_row_contrast :
    (mixed.run (query minByCustomer minByCustomer_one)).returnsResult
      (· = [[.text [65, 67, 77, 69], .integer 5], [.text [122, 101, 116, 97], .integer 7]]) := by
  decide +kernel

#print axioms ordersRows_notNull
#print axioms min_amount
#print axioms joined_customers
#print axioms deciding_row_contrast

end SelectExtremumCases
