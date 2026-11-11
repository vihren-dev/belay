import SelectJoinCases

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Support of the subquery cases A18 and A19 of ADR 0027 over the catalog of {lit}`shop`: a query
over {lit}`customers c` whose {lit}`WHERE` reads subquery 0, the result rule of such a query through
the faultless execution rule ({lit}`Run.query_returnsResult_faultless`), and the run of the
correlated subquery {lit}`SELECT 1 FROM orders o WHERE o.customer_id = c.id` for one customer. -/

namespace SelectSubqueryCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases (cell)
open SelectJoinCases (shop customersShape ordersShape customerRows orderRows shop_found shop_state rows_width)

/-- The query {lit}`SELECT c.name FROM customers c WHERE condition` for a condition that can read
the subqueries of the statement. -/
def customersWhere (condition : Resolved.Expr) : Resolved.Query :=
  { sources := [.first 0], filter := some condition, aggregate := false, groupBy := [],
    columns := [.scalar (.column 1)], names := ["name"], orderBy := [], offset := 0, limit := none }

/-- The condition {lit}`o.customer_id = c.id` of a subquery over {lit}`orders o` inside the query
over {lit}`customers c`: the row of the subquery is the customer, two cells, followed by the order,
so cell 3 is {lit}`o.customer_id` and cell 0 is {lit}`c.id`. -/
def witnessCondition : Resolved.Expr := .compare .eq (some .numeric) (.column 3) (.column 0) .binary

/-- The correlated subquery {lit}`SELECT 1 FROM orders o WHERE o.customer_id = c.id`, after the two
cells of a customer. -/
def witnessQuery : Resolved.Query :=
  { sources := [.first 1], filter := some witnessCondition, aggregate := false, groupBy := [],
    columns := [.scalar (.literal (.integer 1))], names := ["1"], orderBy := [], offset := 0, limit := none,
    outer := 2 }

/-- Whether an order is a witness for a customer: {name}`witnessCondition` is true for the customer
followed by the order, so the order's {lit}`customer_id` equals the customer's id under numeric
affinity. An order with a NULL {lit}`customer_id` is a witness for no customer. -/
def Witness (customer order : List Value) : Bool :=
  Resolved.truthy (witnessCondition.eval (Resolved.EvalContext.bound []) (customer ++ order))

/-- For every database with the catalog of {name}`shop`, the table at position 1 is the table of
{lit}`orders` with the rows of the database. -/
theorem orders_present (db : Database) (schema : db.HasCatalog shop) :
    db.raw.table 1 = some { shape := ordersShape, rows := db.raw.rows.getD 1 [] } :=
  Database.table_of_findTable db.raw _ _ _ (shop_found db schema).2

/-- For every database with the catalog of {name}`shop` and outer row, the run of
{name}`witnessQuery` for the outer row with no values has the result rows of the query over the
orders after the outer cells, and no fault. Proof sketch:
{name}`Resolved.Query.subqueryRun_of_faultless` with {name}`Resolved.Query.sourceAfter_first`; the
expressions of the query are calm. -/
theorem witness_run (db : Database) (schema : db.HasCatalog shop) (outer : List Value) :
    (witnessQuery.subqueryRun (Resolved.EvalContext.bound []) db.raw outer).rows =
        witnessQuery.results (Resolved.EvalContext.bound [])
          ((orderRows db).map (Resolved.outerCells 2 outer ++ ·)) ∧
      (witnessQuery.subqueryRun (Resolved.EvalContext.bound []) db.raw outer).fault = .none := by
  have plain : witnessQuery.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true := by decide +kernel
  have run := Resolved.Query.subqueryRun_of_faultless (Resolved.EvalContext.bound []) db.raw outer none rfl rfl rfl
    (Resolved.Query.sourceAfter_first _ db.raw none witnessQuery 1 _ outer rfl (orders_present db schema)) rfl plain
    (fun row _ expression member => Resolved.Expr.fault_of_plain _ (Resolved.EvalContext.bound_quiet []) row expression
      (by simpa using List.all_eq_true.mp plain expression member))
    (by simp [Resolved.Query.fails, witnessQuery]) (by simp [Resolved.Query.distinctCertain, witnessQuery])
  rw [run]
  exact ⟨rfl, rfl⟩

/-- For every database with the catalog of {name}`shop` and customer row of two cells, the run of
{name}`witnessQuery` for the customer has no rows exactly when no order is a {name}`Witness` for
the customer. Proof sketch: {name}`witness_run` and {name}`Resolved.Query.results_eq_nil_iff_plain`;
the outer cells of a row of two cells are the row. -/
theorem witness_empty (db : Database) (schema : db.HasCatalog shop) {customer : List Value}
    (wide : customer.length = 2) :
    (witnessQuery.subqueryRun (Resolved.EvalContext.bound []) db.raw customer).rows.isEmpty =
      !(orderRows db).any (Witness customer) := by
  have cells : Resolved.outerCells 2 customer = customer := by
    simp [Resolved.outerCells, List.take_of_length_le, wide]
  rw [(witness_run db schema customer).1, cells]
  apply Bool.eq_iff_iff.mpr
  rw [List.isEmpty_iff, Resolved.Query.results_eq_nil_iff_plain _ rfl rfl rfl rfl (by simp [witnessQuery])]
  simp [Resolved.filtered, witnessQuery, Witness, List.filter_eq_nil_iff]

/-- The context of a statement over {name}`customersWhere` with its subqueries and no values. -/
abbrev whereContext (db : Database) (subqueries : List Resolved.Query) : Resolved.EvalContext :=
  Resolved.EvalContext.statement [] db.raw subqueries

/-- For every condition, subqueries, script of {name}`customersWhere` with that condition and
those subqueries, database with the catalog of {name}`shop`, environment and property {lit}`Q` of a
result: when the statement is calm, the condition has no fault for any row, and every permutation
of the names of the customers for which the condition is true has {lit}`Q`, the script returns a
result with {lit}`Q`. Proof sketch: {name}`Run.query_returnsResult_faultless` with the scan of
{lit}`customers` ({name}`Resolved.Query.source_first`), then
{name}`Resolved.Query.perm_of_mem_possibleResults_plain`. -/
theorem customersWhere_returns (condition : Resolved.Expr) (subqueries : List Resolved.Query) (script : Script)
    (one : script.statements.length = 1) (statement : Syntax.Statement) (head : script.statements = [(statement, [])])
    (resolves : resolveStatement runContext (shop.raw.connection {}).resolveState statement =
      .ok (.query (customersWhere condition) subqueries, (shop.raw.connection {}).resolveState))
    (calm : (Resolved.Statement.query (customersWhere condition) subqueries).Calm)
    (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (quiet : ∀ row, (condition.evaluate (whereContext db subqueries) row).2 = .none)
    (property : List (List Value) → Prop)
    (holds : ∀ result, result.Perm (((customerRows db).filter fun customer =>
      Resolved.truthy (condition.eval (whereContext db subqueries) customer)).map fun customer => [cell 1 customer]) →
        property result) :
    (db.run (query script one) env).returnsResult property := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query (customersWhere condition) subqueries, (db.raw.connection env.counters).resolveState) := by
    rw [shop_state db env schema]
    exact resolves
  have found := Resolved.Query.source_first (whereContext db subqueries) (customersWhere condition) db.raw 0 _ rfl
    (Database.table_of_findTable db.raw _ _ _ (shop_found db schema).1)
  rw [Run.query_returnsResult_faultless head one db env resolved found (by simp) calm rfl
    (Resolved.Query.bindWindow_literal _ _ rfl rfl)
    (fun row _ expression member => by
      simp [customersWhere, Resolved.Query.expressions, Resolved.Query.keptExpressions,
        Resolved.QuerySource.expressions, Resolved.QuerySource.first, Resolved.Output.scalars, Resolved.Output.operands] at member
      rcases member with rfl | rfl
      · exact quiet row
      · rfl)
    (by simp [Resolved.Query.fails, customersWhere]) (by simp [Resolved.Query.distinctCertain, customersWhere])]
  intro result member
  apply holds
  have perm := Resolved.Query.perm_of_mem_possibleResults_plain rfl rfl rfl rfl rfl member
  have output : (customersWhere condition).rowOutput (whereContext db subqueries) = fun customer => [cell 1 customer] := by
    funext customer
    simp [Resolved.Query.rowOutput, customersWhere, Resolved.Expr.eval_column]
  rw [output] at perm
  simpa [Resolved.filtered, customersWhere, customerRows] using perm

end SelectSubqueryCases
