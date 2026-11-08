import SelectExtremumCases

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A09, the empty and NULL cases (ADR 0027), through the all-NULL rule
({lit}`Aggregate.eval_allNull`): over every database with the catalog of {lit}`orders` and no stored
row, {lit}`min`, {lit}`max`, {lit}`sum`, {lit}`avg` and {lit}`group_concat` are NULL and
{lit}`total` is 0.0, in one row; over every database with the catalog of {lit}`nullable` whose
customers are all NULL, the same holds for {lit}`customer`, and {lit}`count(customer)` is 0 where
{lit}`count(*)` counts the rows. -/

namespace SelectNullAggregateCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases SelectCountCases SelectExtremumCases

/-- The A09 query of every aggregate of the amounts and the joined customers. -/
def emptyAggregates : Script :=
  sql r"SELECT min(amount), max(amount), sum(amount), avg(amount), total(amount), group_concat(customer) FROM orders"

/-- The query of the aggregates of the amounts has one statement. -/
theorem emptyAggregates_one : emptyAggregates.statements.length = 1 := rfl

/-- The query to which {name}`emptyAggregates` resolves; its last {lit}`max` call decides the row of
the group. -/
def emptyQuery : Resolved.Query :=
  { ungroupedQuery [.aggregate (.min (.column 2) .binary), .aggregate (.max (.column 2) .binary), .aggregate (.sum (.column 2)),
      .aggregate (.avg (.column 2)), .aggregate (.total (.column 2)), .aggregate (.groupConcat (.column 1) none)]
      ["min(amount)", "max(amount)", "sum(amount)", "avg(amount)", "total(amount)", "group_concat(customer)"] with
    deciding := some (.max (.column 2) .binary) }

/-- A09, empty input: for every database with the catalog of {name}`orders` and no stored row, and
every environment, {name}`emptyAggregates` returns one row: NULL for {lit}`min`, {lit}`max`,
{lit}`sum` and {lit}`avg`, the REAL 0.0 for {lit}`total`, and NULL for {lit}`group_concat`. Proof
sketch: as {name}`min_amount`; over no row every operand is NULL, so
{name}`Resolved.Aggregate.eval_allNull` gives each value. -/
theorem empty_aggregates (db : Database) (env : Env) (schema : db.HasCatalog orders) (empty : ordersRows db = []) :
    (db.run (query emptyAggregates emptyAggregates_one) env).returnsResult
      (· = [[.null, .null, .null, .null, realValue (Float.ofInt 0), .null]]) := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (match emptyAggregates.statements with | (statement, _) :: _ => statement | [] => .begin) =
      .ok (.query emptyQuery [], (db.raw.connection env.counters).resolveState) := by
    rw [orders_state db env schema]
    decide +kernel
  rw [Run.query_returnsResult_calmTable (script := emptyAggregates) rfl emptyAggregates_one db env resolved rfl
    (Database.table_of_findTable db.raw _ _ _ (orders_found db schema)) (by unfold Resolved.Statement.Calm; decide)
    rfl rfl rfl (by change emptyQuery.fails _ (ordersRows db) = false; rw [empty]; decide +kernel) rfl]
  intro result member
  rw [result_ungrouped rfl rfl rfl rfl rfl rfl rfl rfl member]
  change [(emptyQuery.groupRecord (Resolved.EvalContext.bound []) (ordersRows db)).1] = _
  rw [empty]
  obtain ⟨-, sum, -, avg, total, min, max, -⟩ :=
    Resolved.Aggregate.eval_allNull (Resolved.EvalContext.bound []) [] (.column 2) .binary nofun
  obtain ⟨-, -, -, -, -, -, -, concat⟩ :=
    Resolved.Aggregate.eval_allNull (Resolved.EvalContext.bound []) [] (.column 1) .binary nofun
  simp [Resolved.Query.groupRecord, emptyQuery, ungroupedQuery, sum, avg, total, min, max, concat]

/-- The catalog table of {name}`nullable`. -/
def nullableShape : CatalogTable := ((nullable.raw.catalog.findTable (name! "orders")).get (by decide +kernel)).2

/-- The scan of the table {lit}`orders` of a database with the catalog of {name}`nullable`. -/
abbrev nullableRows (db : Database) : List (List Value) :=
  Resolved.sourceRows { shape := nullableShape, rows := db.raw.rows.getD 0 [] }

/-- For every database with the catalog of {name}`nullable`, the table {lit}`orders` is at position 0
with {name}`nullableShape`. Proof sketch: the lookup reads only the catalog. -/
theorem nullable_found (db : Database) (schema : db.HasCatalog nullable) :
    db.raw.catalog.findTable (name! "orders") = some (0, nullableShape) := by
  rw [show db.raw.catalog = nullable.raw.catalog from schema]
  decide +kernel

/-- The A09 query of every aggregate of the customers, and the number of rows. -/
def nullCustomers : Script :=
  sql r"SELECT min(customer), max(customer), sum(customer), group_concat(customer), count(customer), count(*) FROM orders"

/-- The query of the aggregates of the customers has one statement. -/
theorem nullCustomers_one : nullCustomers.statements.length = 1 := rfl

/-- The query to which {name}`nullCustomers` resolves; its last {lit}`max` call decides the row of
the group. -/
def nullQuery : Resolved.Query :=
  { ungroupedQuery [.aggregate (.min (.column 1) .binary), .aggregate (.max (.column 1) .binary), .aggregate (.sum (.column 1)),
      .aggregate (.groupConcat (.column 1) none), .aggregate (.count (.column 1)), .aggregate .countRows]
      ["min(customer)", "max(customer)", "sum(customer)", "group_concat(customer)", "count(customer)", "count(*)"] with
    deciding := some (.max (.column 1) .binary) }

/-- A09, NULL input: for every database with the catalog of {name}`nullable` whose customer is NULL
on every row of the scan, and every environment, {name}`nullCustomers` returns one row: NULL for
{lit}`min`, {lit}`max`, {lit}`sum` and {lit}`group_concat`, 0 for {lit}`count(customer)`, and the
number of rows for {lit}`count(*)`. Proof sketch: as {name}`empty_aggregates`, with the premise in
place of no row, and {name}`Resolved.countRows_eval`. -/
theorem null_customers (db : Database) (env : Env) (schema : db.HasCatalog nullable)
    (nulls : ∀ row ∈ nullableRows db, (cell 1 row).isNull = true) :
    (db.run (query nullCustomers nullCustomers_one) env).returnsResult
      (· = [[.null, .null, .null, .null, .integer 0, .integer (nullableRows db).length]]) := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (match nullCustomers.statements with | (statement, _) :: _ => statement | [] => .begin) =
      .ok (.query nullQuery [], (db.raw.connection env.counters).resolveState) := by
    have state : (db.raw.connection env.counters).resolveState = (nullable.raw.connection {}).resolveState := by
      simp only [Connection.resolveState, Database.Raw.connection]
      rw [show db.raw.catalog = nullable.raw.catalog from schema]
    rw [state]
    decide +kernel
  have safe : nullQuery.fails (Resolved.EvalContext.bound []) (nullableRows db) = false := by
    generalize nullableRows db = rows at nulls
    have := (Resolved.Aggregate.eval_allNull (Resolved.EvalContext.bound []) rows (.column 1) .binary nulls).2.2.1
    rw [Resolved.Query.fails, Resolved.filtered_of_filter_none _ (query := nullQuery) rfl,
      Resolved.queryGroups_ungrouped _ (query := nullQuery) rfl]
    simp only [nullQuery, ungroupedQuery, List.any_cons, List.any_nil, this]
    simp [Resolved.Aggregate.fails]
  rw [Run.query_returnsResult_calmTable (script := nullCustomers) rfl nullCustomers_one db env resolved rfl
    (Database.table_of_findTable db.raw _ _ _ (nullable_found db schema)) (by unfold Resolved.Statement.Calm; decide)
    rfl rfl rfl safe rfl]
  intro result member
  rw [result_ungrouped rfl rfl rfl rfl rfl rfl rfl rfl member]
  change [(nullQuery.groupRecord (Resolved.EvalContext.bound []) (nullableRows db)).1] = _
  generalize nullableRows db = rows at nulls ⊢
  obtain ⟨count, sum, -, -, -, min, max, concat⟩ :=
    Resolved.Aggregate.eval_allNull (Resolved.EvalContext.bound []) rows (.column 1) .binary nulls
  simp [Resolved.Query.groupRecord, nullQuery, ungroupedQuery, count, sum, min, max, concat, Resolved.countRows_eval]

/-- A09 instances: {name}`orders` has no row, and the one customer of {name}`nullable` is NULL. -/
example : (orders.run (query emptyAggregates emptyAggregates_one)).returnsResult
      (· = [[.null, .null, .null, .null, realValue (Float.ofInt 0), .null]]) ∧
    (nullable.run (query nullCustomers nullCustomers_one)).returnsResult
      (· = [[.null, .null, .null, .null, .integer 0, .integer 1]]) :=
  ⟨empty_aggregates orders Env.default rfl (by decide +kernel),
    (null_customers nullable Env.default rfl (by decide +kernel)).mono fun _ same => by rw [same]; decide +kernel⟩

#print axioms empty_aggregates
#print axioms nullable_found
#print axioms null_customers

end SelectNullAggregateCases
