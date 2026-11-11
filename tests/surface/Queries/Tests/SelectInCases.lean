import SelectSubquerySupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A19 of ADR 0027 for {lit}`IN`, through the subquery rules
({lit}`Resolved.Query.subqueryRun_of_faultless`, {lit}`Resolved.Query.results_plain_unordered`)
over every database with the catalog of {lit}`shop`: {lit}`c.id IN (SELECT o.customer_id FROM
orders o)` reads the first column of the subquery's rows, and its value follows the NULL rules of
{lit}`IN` ({lit}`Resolved.inValue`): {lit}`NOT IN` over a list with NULL is never true. -/

namespace SelectSubqueryCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases (cell)
open SelectJoinCases (shop customerRows orderRows rows_width partial_)

/-- The subquery {lit}`SELECT o.customer_id FROM orders o`, after the two cells of a customer: cell
3 of its row is {lit}`o.customer_id`. -/
def customerIdsQuery : Resolved.Query :=
  { sources := [.first 1], filter := none, aggregate := false, groupBy := [], columns := [.scalar (.column 3)],
    names := ["customer_id"], orderBy := [], offset := 0, limit := none, outer := 2 }

/-- For every database with the catalog of {name}`shop` and outer row, the run of
{name}`customerIdsQuery` for the outer row with no values has one row for each order, in scan
order, with its {lit}`customer_id`; no fault; and certain rows. Proof sketch:
{name}`Resolved.Query.subqueryRun_of_faultless` and {name}`Resolved.Query.results_plain_unordered`;
the outer cells have two cells ({name}`Resolved.outerCells_length`). -/
theorem customerIds_run (db : Database) (schema : db.HasCatalog shop) (outer : List Value) :
    (customerIdsQuery.subqueryRun (Resolved.EvalContext.bound []) db.raw outer).rows =
        (orderRows db).map (fun order => [cell 1 order]) ∧
      (customerIdsQuery.subqueryRun (Resolved.EvalContext.bound []) db.raw outer).fault = .none ∧
      (customerIdsQuery.subqueryRun (Resolved.EvalContext.bound []) db.raw outer).rowsCertain = true := by
  have plain : customerIdsQuery.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true := by decide +kernel
  have run := Resolved.Query.subqueryRun_of_faultless (Resolved.EvalContext.bound []) db.raw outer none rfl rfl rfl
    (Resolved.Query.sourceAfter_first _ db.raw none customerIdsQuery 1 _ outer rfl (orders_present db schema)) rfl plain
    (fun row _ expression member => Resolved.Expr.fault_of_plain _ (Resolved.EvalContext.bound_quiet []) row expression
      (by simpa using List.all_eq_true.mp plain expression member))
    (by simp [Resolved.Query.fails, customerIdsQuery]) (by simp [Resolved.Query.distinctCertain, customerIdsQuery])
  have width := Resolved.outerCells_length 2 outer
  rw [run]
  refine ⟨?_, rfl, by simp [Resolved.Query.windowCertain, Resolved.certainCut, customerIdsQuery]⟩
  rw [Resolved.Query.results_plain_unordered _ rfl rfl rfl rfl rfl rfl, Resolved.filtered_of_filter_none _ rfl]
  simp only [List.map_map]
  refine List.map_congr_left fun order _ => ?_
  simp [Resolved.Query.rowOutput, customerIdsQuery, Resolved.Expr.eval_column, List.getElem?_append_right, width]

/-- The condition {lit}`c.id IN (subquery 0)`, or {lit}`c.id NOT IN (subquery 0)` when negated. -/
def idIn (negated : Bool) : Resolved.Expr := .inQuery (.column 0) 0 (some .numeric) .binary negated

/-- Whether {lit}`IN` keeps a customer: the value of {lit}`IN` ({name}`Resolved.inValue`) for the
customer's id over the {lit}`customer_id` of every order is true. -/
def KeptByIn (db : Database) (negated : Bool) (customer : List Value) : Bool :=
  Resolved.truthy (Resolved.inValue (some .numeric) .binary negated (cell 0 customer) ((orderRows db).map (cell 1 ·)))

/-- For every negation, script of {name}`customersWhere` with {name}`idIn` and subquery
{name}`customerIdsQuery`, database with the catalog of {name}`shop` and environment, the script
returns a result that is a permutation of the names of the customers that {name}`KeptByIn` keeps.
Proof sketch: {name}`customersWhere_returns`; the run of the subquery has no fault and certain rows,
and its first column is the {lit}`customer_id` of every order ({name}`customerIds_run`). -/
theorem in_returns (negated : Bool) (script : Script) (one : script.statements.length = 1)
    (statement : Syntax.Statement) (head : script.statements = [(statement, [])])
    (resolves : resolveStatement runContext (shop.raw.connection {}).resolveState statement =
      .ok (.query (customersWhere (idIn negated)) [customerIdsQuery], (shop.raw.connection {}).resolveState))
    (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (db.run (query script one) env).returnsResult fun result =>
      result.Perm (((customerRows db).filter (KeptByIn db negated)).map fun customer => [cell 1 customer]) :=
  customersWhere_returns (idIn negated) [customerIdsQuery] script one statement head resolves
    (by unfold Resolved.Statement.Calm; cases negated <;> decide +kernel) db env schema
    (fun row => by
      obtain ⟨-, fault, certain⟩ := customerIds_run db schema row
      simp [idIn, Resolved.Expr.evaluate, Resolved.EvalContext.statement_one, fault, certain, Resolved.Fault.join])
    _ fun result perm => by
      have kept : ∀ customer, Resolved.truthy ((idIn negated).eval (whereContext db [customerIdsQuery]) customer) =
          KeptByIn db negated customer := fun customer => by
        rw [idIn, Resolved.Expr.eval_inQuery, Resolved.EvalContext.statement_one, (customerIds_run db schema customer).1]
        simp [KeptByIn, List.filterMap_map, Resolved.Expr.eval_column, Function.comp_def]
      rwa [List.filter_congr fun customer _ => kept customer] at perm

/-- The query of A19 with {lit}`IN`. -/
def inScript : Script := sql r"SELECT c.name FROM customers c WHERE c.id IN (SELECT o.customer_id FROM orders o)"

/-- The query of A19 with {lit}`NOT IN`. -/
def notInScript : Script :=
  sql r"SELECT c.name FROM customers c WHERE c.id NOT IN (SELECT o.customer_id FROM orders o)"

/-- A19 with {lit}`IN`: for every database with the catalog of {name}`shop` and every environment,
the query returns a result that is a permutation of the names of the customers whose id is among
the {lit}`customer_id` values of the orders under {lit}`IN` ({name}`KeptByIn`). -/
theorem in_subquery (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (db.run (query inScript rfl) env).returnsResult fun result =>
      result.Perm (((customerRows db).filter (KeptByIn db false)).map fun customer => [cell 1 customer]) :=
  in_returns false inScript rfl _ rfl (by decide +kernel) db env schema

/-- A19 with {lit}`NOT IN`: as {name}`in_subquery` with the negated value of {lit}`IN`. -/
theorem not_in_subquery (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (db.run (query notInScript rfl) env).returnsResult fun result =>
      result.Perm (((customerRows db).filter (KeptByIn db true)).map fun customer => [cell 1 customer]) :=
  in_returns true notInScript rfl _ rfl (by decide +kernel) db env schema

/-- A19 contrast for {lit}`IN`: on {name}`partial_` the orders have the {lit}`customer_id` values
1, 9 and NULL. {lit}`IN` keeps {lit}`acme`; {lit}`NOT IN` keeps no customer, because
{lit}`2 NOT IN (1, 9, NULL)` is NULL, not true. Native SQLite 3.51.0 gives the same rows. -/
example : (partial_.run (query inScript rfl)).returnsResult (· = [[.text "acme".toUTF8.toList]]) ∧
    (partial_.run (query notInScript rfl)).returnsResult (· = []) := by
  decide +kernel

example : Resolved.inValue (some .numeric) .binary true (.integer 2) [.integer 1, .integer 9, .null] = .null := by
  decide +kernel

#print axioms customerIds_run
#print axioms in_returns
#print axioms in_subquery
#print axioms not_in_subquery

end SelectSubqueryCases
