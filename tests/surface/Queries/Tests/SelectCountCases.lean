import SelectGroupCases

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance cases of the aggregate rules of ADR 0027 for {lit}`count`: A08, {lit}`count(*)` without
{lit}`GROUP BY` gives one row with the number of stored rows, also 0 for an empty table, and a grouped
query over an empty table gives no row; and the count rule of A09, {lit}`count(customer)` is
{lit}`count(*)` for a NOT NULL column, over every database with the catalog of {lit}`orders`. -/

namespace SelectCountCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases

/-- The A08 query: the number of orders. -/
def countAll : Script := sql r"SELECT count(*) FROM orders"

/-- The A08 query has one statement. -/
theorem countAll_one : countAll.statements.length = 1 := rfl

/-- The query to which an ungrouped aggregate query of {lit}`orders` resolves: its result columns, with
no condition, grouping or sort. -/
def ungroupedQuery (columns : List Resolved.Output) (names : List String) : Resolved.Query :=
  { sources := [.first 0], filter := none, aggregate := true, groupBy := [], columns, names, orderBy := [], offset := 0,
    limit := none }

/-- A08 with the catalog fact: for every database with the catalog of {name}`orders` and every
environment, {name}`countAll` returns one row with the number of stored rows of {lit}`orders`
({name}`ordersRows`), also the row of 0 when the table has no row. Proof sketch: for the catalog the
statement resolves to {name}`ungroupedQuery` of {lit}`count(*)`; {name}`Run.query_returnsResult_calmTable`
and {name}`result_ungrouped` give the one row of the group of all rows, whose value is the number of
rows ({name}`Resolved.countRows_eval`). -/
theorem count_rows (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query countAll countAll_one) env).returnsResult (· = [[.integer (ordersRows db).length]]) := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (match countAll.statements with | (statement, _) :: _ => statement | [] => .begin) =
      .ok (.query (ungroupedQuery [.aggregate .countRows] ["count(*)"]) [], (db.raw.connection env.counters).resolveState) := by
    rw [orders_state db env schema]
    decide +kernel
  rw [Run.query_returnsResult_calmTable (script := countAll) rfl countAll_one db env resolved rfl
    (Database.table_of_findTable db.raw _ _ _ (orders_found db schema)) (by unfold Resolved.Statement.Calm; decide)
    rfl rfl rfl (by simp [Resolved.Query.fails, ungroupedQuery, Resolved.Aggregate.fails_countRows]) rfl]
  intro result member
  rw [result_ungrouped rfl rfl rfl rfl rfl rfl rfl rfl member]
  simp [Resolved.Query.groupRecord, ungroupedQuery, Resolved.countRows_eval]
  rfl

/-- A08 for a grouped query: for every database with the catalog of {name}`orders` and no stored row of
{lit}`orders`, and every environment, {name}`byCustomer` returns no row: an empty table has no group.
Proof sketch: the result of {name}`customer_counts` has a group for each row, because the groups are
a partition of the rows and each group has a row ({name}`KeyPartition.ne_nil`). -/
theorem grouped_empty (db : Database) (env : Env) (schema : db.HasCatalog orders) (empty : ordersRows db = []) :
    (db.run (query byCustomer byCustomer_one) env).returnsResult (· = []) := by
  refine (customer_counts db env schema).mono fun result counts => ?_
  obtain ⟨found, partition, ⟨pick, -, rfl⟩, -⟩ := counts
  rw [empty] at partition
  cases found with
  | nil => rfl
  | cons group rest =>
    have length := partition.1.length_eq
    have nonempty := partition.ne_nil (List.mem_cons_self ..)
    simp only [List.flatten_cons, List.length_append, List.length_nil] at length
    exact absurd (List.length_eq_zero_iff.mp (by omega)) nonempty

/-- A08 contrast: an empty source does not make an empty aggregate result. {name}`orders` has no
order, and {name}`countAll` returns the row of 0 there, not an empty result. -/
theorem empty_source_contrast :
    (orders.run (query countAll countAll_one)).returnsResult (· = [[.integer 0]]) ∧
      ¬ (orders.run (query countAll countAll_one)).returnsResult (· = []) :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- The count query of A09: the number of customer cells that are not NULL, and the number of
orders. -/
def countCustomers : Script := sql r"SELECT count(customer), count(*) FROM orders"

/-- The A09 count query has one statement. -/
theorem countCustomers_one : countCustomers.statements.length = 1 := rfl

/-- A09 count rule: for every database with the catalog of {name}`orders` and every environment,
{name}`countCustomers` returns one row whose two cells are both the number of stored rows: the
column {lit}`customer` is NOT NULL, so {lit}`count(customer)` is {lit}`count(*)`. Proof sketch: as
{name}`count_rows`; the validity of the database ({name}`Database.notNull`) makes every customer cell
not NULL, and {name}`Resolved.Aggregate.eval_count_of_notNull` gives the count. -/
theorem count_customers (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query countCustomers countCustomers_one) env).returnsResult
      (· = [[.integer (ordersRows db).length, .integer (ordersRows db).length]]) := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (match countCustomers.statements with | (statement, _) :: _ => statement | [] => .begin) =
      .ok (.query (ungroupedQuery [.aggregate (.count (.column 1)), .aggregate .countRows]
        ["count(customer)", "count(*)"]) [], (db.raw.connection env.counters).resolveState) := by
    rw [orders_state db env schema]
    decide +kernel
  have present := Database.table_of_findTable db.raw _ _ _ (orders_found db schema)
  rw [Run.query_returnsResult_calmTable (script := countCustomers) rfl countCustomers_one db env resolved rfl present
    (by unfold Resolved.Statement.Calm; decide) rfl rfl rfl
    (by simp [Resolved.Query.fails, ungroupedQuery, Resolved.Aggregate.fails]) rfl]
  intro result member
  rw [result_ungrouped rfl rfl rfl rfl rfl rfl rfl rfl member]
  have notNull : ∀ row ∈ ordersRows db, ((Resolved.Expr.column 1).eval (Resolved.EvalContext.bound []) row).isNull =
      false := by
    intro row inRows
    obtain ⟨stored, storedIn, rfl⟩ := (mem_sourceRows_iff _ row).mp inRows
    have wide := db.valid.admitted.rowsWide 0 _ present stored storedIn
    have inside : 1 < stored.values.length := wide ▸ (by decide +kernel : 1 < ordersShape.columns.length)
    have cell := db.notNull 0 _ present stored storedIn 1 (ordersShape.columns[1]'(by decide +kernel)) _
      (by simp) (List.getElem?_eq_getElem inside) (by decide +kernel)
    simp [Resolved.Expr.eval_column, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Value.isNull]
    cases h : stored.values[1] <;> simp_all
  change [((ungroupedQuery [.aggregate (.count (.column 1)), .aggregate .countRows] ["count(customer)", "count(*)"]).groupRecord
    (Resolved.EvalContext.bound []) (ordersRows db)).1] = _
  generalize ordersRows db = rows at notNull ⊢
  simp [Resolved.Query.groupRecord, ungroupedQuery, Resolved.Aggregate.eval_count_of_notNull _ _ _ notNull,
    Resolved.countRows_eval]

/-- An order whose customer is NULL, in a table whose column {lit}`customer` accepts NULL. -/
def nullable : Database := db! r"
  CREATE TABLE orders (id INTEGER PRIMARY KEY, customer TEXT, amount INTEGER NOT NULL);
  INSERT INTO orders VALUES (1, NULL, 10);"

/-- A09 count contrast: without NOT NULL, {lit}`count(customer)` is not {lit}`count(*)`. On
{name}`nullable` the query returns 0 and 1. -/
theorem nullable_count_contrast :
    (nullable.run (query countCustomers countCustomers_one)).returnsResult (· = [[.integer 0, .integer 1]]) := by
  decide +kernel

#print axioms count_rows
#print axioms grouped_empty
#print axioms empty_source_contrast
#print axioms count_customers
#print axioms nullable_count_contrast

end SelectCountCases
