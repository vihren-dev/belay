import SelectSubquerySupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A19 of ADR 0027 for a scalar subquery, through the subquery rules
({lit}`Resolved.Query.subqueryRun_of_faultless`, {lit}`Resolved.Query.results_plain_unordered`,
{lit}`Resolved.Query.windowCertain_of_short`) over every database with the catalog of
{lit}`shop`: the correlated scalar subquery {lit}`(SELECT o.amount FROM orders o WHERE
o.customer_id = c.id)` reads the first value of the first row, and NULL when the subquery has no
row. With more than one matching order the first row depends on SQLite's plan, so the rule needs
at most one witness for each customer. -/

namespace SelectSubqueryCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases (cell)
open SelectJoinCases (shop customerRows orderRows rows_width shop_found shop_state partial_)

/-- The correlated subquery {lit}`SELECT o.amount FROM orders o WHERE o.customer_id = c.id`, after
the two cells of a customer: cell 4 of its row is {lit}`o.amount`. -/
def amountQuery : Resolved.Query :=
  { sources := [.first 1], filter := some witnessCondition, aggregate := false, groupBy := [],
    columns := [.scalar (.column 4)], names := ["amount"], orderBy := [], offset := 0, limit := none, outer := 2 }

/-- The query {lit}`SELECT c.name, (subquery 0) FROM customers c`. -/
def amountsQuery : Resolved.Query :=
  { sources := [.first 0], filter := none, aggregate := false, groupBy := [],
    columns := [.scalar (.column 1), .scalar (.subquery 0)],
    names := ["name", "(SELECT o.amount FROM orders o WHERE o.customer_id = c.id)"], orderBy := [], offset := 0,
    limit := none }

/-- The value of the scalar subquery for a customer: the amount of the first order that is a
{name}`Witness` for the customer, or NULL when there is none. -/
def firstAmount (db : Database) (customer : List Value) : Value :=
  (((orderRows db).find? (Witness customer)).map (cell 2 ·)).getD .null

/-- For every database with the catalog of {name}`shop` and outer row, the run of
{name}`amountQuery` for the outer row with no values has the amount of each order that is a
{name}`Witness` for the outer cells, in scan order, and no fault; its first value is certain when at
most one order is a witness. Proof sketch: {name}`Resolved.Query.subqueryRun_of_faultless`,
{name}`Resolved.Query.results_plain_unordered` and {name}`Resolved.Query.windowCertain_of_short`. -/
theorem amount_run (db : Database) (schema : db.HasCatalog shop) (outer : List Value) :
    (amountQuery.subqueryRun (Resolved.EvalContext.bound []) db.raw outer).rows =
        ((orderRows db).filter (Witness (Resolved.outerCells 2 outer))).map (fun order => [cell 2 order]) ∧
      (amountQuery.subqueryRun (Resolved.EvalContext.bound []) db.raw outer).fault = .none ∧
      ((orderRows db).countP (Witness (Resolved.outerCells 2 outer)) ≤ 1 →
        (amountQuery.subqueryRun (Resolved.EvalContext.bound []) db.raw outer).firstCertain = true) := by
  have plain : amountQuery.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true := by decide +kernel
  have run := Resolved.Query.subqueryRun_of_faultless (Resolved.EvalContext.bound []) db.raw outer none rfl rfl rfl
    (Resolved.Query.sourceAfter_first _ db.raw none amountQuery 1 _ outer rfl (orders_present db schema)) rfl plain
    (fun row _ expression member => Resolved.Expr.fault_of_plain _ (Resolved.EvalContext.bound_quiet []) row expression
      (by simpa using List.all_eq_true.mp plain expression member))
    (by simp [Resolved.Query.fails, amountQuery]) (by simp [Resolved.Query.distinctCertain, amountQuery])
  have width := Resolved.outerCells_length 2 outer
  have outerTwo : amountQuery.outer = 2 := rfl
  have source : Resolved.sourceRows { shape := SelectJoinCases.ordersShape, rows := db.raw.rows.getD 1 [] } =
      orderRows db := rfl
  have kept : Resolved.filtered (Resolved.EvalContext.bound []) amountQuery
      ((orderRows db).map (Resolved.outerCells 2 outer ++ ·)) =
      ((orderRows db).filter (Witness (Resolved.outerCells 2 outer))).map (Resolved.outerCells 2 outer ++ ·) := by
    simp [Resolved.filtered, amountQuery, List.filter_map, Function.comp_def]
    rfl
  rw [run]
  refine ⟨?_, rfl, fun short => ?_⟩
  · rw [Resolved.Query.results_plain_unordered _ rfl rfl rfl rfl rfl rfl]
    dsimp only
    rw [outerTwo, source, kept, List.map_map]
    refine List.map_congr_left fun order _ => ?_
    simp [Resolved.Query.rowOutput, amountQuery, Resolved.Expr.eval_column, List.getElem?_append_right, width]
  · dsimp only
    refine Resolved.Query.windowCertain_of_short _ rfl ?_ _ _
    have outputs := congrArg List.length (amountQuery.uniqueRecords_outputs_plain (Resolved.EvalContext.bound [])
      rfl rfl rfl ((orderRows db).map (Resolved.outerCells 2 outer ++ ·)))
    simp only [List.length_map] at outputs
    rw [outerTwo, source, outputs, kept, List.length_map, ← List.countP_eq_length_filter]
    exact short

/-- For every order, no order is a {name}`Witness` for the outer cells of the row without cells,
which are NULL: a comparison with NULL is not true. -/
theorem witness_null (order : List Value) : Witness (Resolved.outerCells 2 []) order = false := by
  simp [Witness, witnessCondition, Resolved.outerCells, Resolved.Expr.eval, Resolved.Expr.evaluate]
  rw [Resolved.truthy_apply_ordinary _ (by decide) (by decide)]
  simp [(Resolved.comparisonOperands_isNull (some .numeric) _ .null).2]

/-- The query of A19 with a scalar subquery. -/
def amountsScript : Script :=
  sql r"SELECT c.name, (SELECT o.amount FROM orders o WHERE o.customer_id = c.id) FROM customers c"

/-- A19 with a scalar subquery: for every database with the catalog of {name}`shop` and every
environment, when at most one order is a {name}`Witness` for each customer, the query returns a
result that is a permutation of the name of each customer with {name}`firstAmount`: the amount of
its order, or NULL when it has none. Proof sketch: {name}`Run.query_returnsResult_faultless`; the
run of the subquery has no fault and a certain first value for each customer and for the row
without cells ({name}`amount_run`, {name}`witness_null`), and its first value is the amount of the
first witness. -/
theorem scalar_amounts (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (atMostOne : ∀ customer ∈ customerRows db, (orderRows db).countP (Witness customer) ≤ 1) :
    (db.run (query amountsScript rfl) env).returnsResult fun result =>
      result.Perm ((customerRows db).map fun customer => [cell 1 customer, firstAmount db customer]) := by
  obtain ⟨statement, head, resolves⟩ : ∃ statement, amountsScript.statements = [(statement, [])] ∧
      resolveStatement runContext (shop.raw.connection {}).resolveState statement =
        .ok (.query amountsQuery [amountQuery], (shop.raw.connection {}).resolveState) := ⟨_, rfl, by decide +kernel⟩
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query amountsQuery [amountQuery], (db.raw.connection env.counters).resolveState) := by
    rw [shop_state db env schema]
    exact resolves
  have found := Resolved.Query.source_first (whereContext db [amountQuery]) amountsQuery db.raw 0 _ rfl
    (Database.table_of_findTable db.raw _ _ _ (shop_found db schema).1)
  have cells : ∀ customer ∈ customerRows db, Resolved.outerCells 2 customer = customer := fun customer member => by
    simp [Resolved.outerCells, List.take_of_length_le, (rows_width db schema).2 customer member]
  have certain : ∀ row ∈ [] :: customerRows db,
      (amountQuery.subqueryRun (Resolved.EvalContext.bound []) db.raw row).firstCertain = true := by
    intro row member
    rcases List.mem_cons.mp member with rfl | member
    · exact (amount_run db schema []).2.2 (by rw [List.countP_eq_zero.mpr fun order _ => by simp [witness_null]]; omega)
    · exact (amount_run db schema row).2.2 (by rw [cells row member]; exact atMostOne row member)
  rw [Run.query_returnsResult_faultless head rfl db env resolved found (by simp)
    (by unfold Resolved.Statement.Calm; decide +kernel) rfl
    (Resolved.Query.bindWindow_literal _ _ rfl rfl)
    (fun row member expression inside => by
      simp [amountsQuery, Resolved.Query.expressions, Resolved.Query.keptExpressions,
        Resolved.QuerySource.expressions, Resolved.QuerySource.first, Resolved.Output.scalars, Resolved.Output.operands] at inside
      rcases inside with rfl | rfl
      · rfl
      · simp [Resolved.Expr.evaluate, Resolved.EvalContext.statement_one, certain row member,
          (amount_run db schema row).2.1])
    (by simp [Resolved.Query.fails, amountsQuery]) (by simp [Resolved.Query.distinctCertain, amountsQuery])]
  intro result member
  have perm := Resolved.Query.perm_of_mem_possibleResults_plain rfl rfl rfl rfl rfl member
  rw [Resolved.filtered_of_filter_none _ rfl] at perm
  refine perm.trans (List.Perm.of_eq (List.map_congr_left fun customer inside => ?_))
  simp [Resolved.Query.rowOutput, amountsQuery, Resolved.Expr.eval_subquery, Resolved.EvalContext.statement_one,
    (amount_run db schema customer).1, cells customer inside, firstAmount, List.head?_map, List.head?_filter]
  refine ⟨rfl, ?_⟩
  cases (orderRows db).find? (Witness customer) <;> rfl

/-- A19 contrast for a scalar subquery: on {name}`partial_` {lit}`acme` has one order, with the
amount 10, and {lit}`zeta` has none, so its scalar subquery is NULL. Native SQLite 3.51.0 gives the
same rows. -/
example : (partial_.run (query amountsScript rfl)).returnsResult
    (· = [[.text "acme".toUTF8.toList, .integer 10], [.text "zeta".toUTF8.toList, .null]]) := by
  decide +kernel

#print axioms amount_run
#print axioms scalar_amounts

end SelectSubqueryCases
