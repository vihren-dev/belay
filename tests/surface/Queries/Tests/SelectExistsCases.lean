import SelectSubquerySupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A18 of ADR 0027, through the subquery rules
({lit}`Resolved.EvalContext.statement_one`, {lit}`Resolved.Query.subqueryRun_of_faultless`,
{lit}`Resolved.Query.results_eq_nil_iff_plain`) over every database with the catalog of
{lit}`shop`: a correlated {lit}`EXISTS` keeps exactly the customers for which some order is a
witness, and {lit}`NOT EXISTS` exactly the others. The subquery runs once for each customer, so the
proof reads its run for each outer row. -/

namespace SelectSubqueryCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases (cell)
open SelectJoinCases (shop customerRows orderRows rows_width partial_)

/-- The names of the customers for which the test on their witnesses is true, in scan order. -/
def namesWhere (db : Database) (test : Bool → Bool) : List (List Value) :=
  ((customerRows db).filter fun customer => test ((orderRows db).any (Witness customer))).map
    fun customer => [cell 1 customer]

/-- For every database with the catalog of {name}`shop`, a test on Booleans and a condition that
reads the emptiness of the run of {name}`witnessQuery` for a customer through the test, the result
rule of {name}`customersWhere_returns` gives the names of {name}`namesWhere`. Proof sketch: each
customer row has two cells ({name}`rows_width`), so {name}`witness_empty` gives the emptiness. -/
theorem filter_witness (db : Database) (schema : db.HasCatalog shop) (condition : Resolved.Expr) (test : Bool → Bool)
    (reads : ∀ customer, Resolved.truthy (condition.eval (whereContext db [witnessQuery]) customer) =
      test !(witnessQuery.subqueryRun (Resolved.EvalContext.bound []) db.raw customer).rows.isEmpty) :
    ((customerRows db).filter fun customer =>
      Resolved.truthy (condition.eval (whereContext db [witnessQuery]) customer)).map (fun customer => [cell 1 customer]) =
      namesWhere db test := by
  rw [namesWhere, List.filter_congr fun customer member => by
    rw [reads, witness_empty db schema ((rows_width db schema).2 customer member), Bool.not_not]]

/-- The query of A18: the customers with an order. -/
def existsScript : Script :=
  sql r"SELECT c.name FROM customers c WHERE EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.id)"

/-- The query of A18 with {lit}`NOT EXISTS`: the customers without an order. -/
def notExistsScript : Script :=
  sql r"SELECT c.name FROM customers c WHERE NOT EXISTS (SELECT 1 FROM orders o WHERE o.customer_id = c.id)"

/-- A18: for every database with the catalog of {name}`shop` and every environment, the correlated
{lit}`EXISTS` returns a result that is a permutation of the names of the customers for which some
order is a {name}`Witness`. Proof sketch: {name}`customersWhere_returns`; the run of the subquery
for each customer has no fault ({name}`witness_run`), and its rows are empty exactly when no order
is a witness ({name}`filter_witness`). -/
theorem exists_witness (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (db.run (query existsScript rfl) env).returnsResult fun result => result.Perm (namesWhere db id) :=
  customersWhere_returns (.exists 0) [witnessQuery] existsScript rfl _ rfl (by decide +kernel)
    (by unfold Resolved.Statement.Calm; decide +kernel) db env schema
    (fun row => by rw [Resolved.Expr.fault_exists, Resolved.EvalContext.statement_one]; exact (witness_run db schema row).2)
    _ fun result perm => by
      rwa [filter_witness db schema _ id fun customer => by
        rw [Resolved.Expr.eval_exists, Resolved.EvalContext.statement_one]
        cases (witnessQuery.subqueryRun (Resolved.EvalContext.bound []) db.raw customer).rows.isEmpty <;> rfl] at perm

/-- A18 with {lit}`NOT EXISTS`: for every database with the catalog of {name}`shop` and every
environment, the query returns a result that is a permutation of the names of the customers for
which no order is a {name}`Witness`. Proof sketch: as {name}`exists_witness`; {lit}`NOT` turns the
test around ({name}`Resolved.truthy_not`). -/
theorem not_exists_witness (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (db.run (query notExistsScript rfl) env).returnsResult fun result => result.Perm (namesWhere db (!·)) :=
  customersWhere_returns (.not (.exists 0)) [witnessQuery] notExistsScript rfl _ rfl (by decide +kernel)
    (by unfold Resolved.Statement.Calm; decide +kernel) db env schema
    (fun row => by
      rw [Resolved.Expr.fault_not, Resolved.Expr.fault_exists, Resolved.EvalContext.statement_one]
      exact (witness_run db schema row).2)
    _ fun result perm => by
      rwa [filter_witness db schema _ (!·) fun customer => by
        rw [Resolved.Expr.eval_not, Resolved.truthy_not, Resolved.Expr.eval_exists, Resolved.EvalContext.statement_one]
        cases (witnessQuery.subqueryRun (Resolved.EvalContext.bound []) db.raw customer).rows.isEmpty <;> rfl] at perm

/-- A18 contrast, with two outer rows: on {name}`partial_` the run of the subquery for
{lit}`acme` has a row and the run for {lit}`zeta` has none, so a proof of the subquery for one
customer does not serve the other. {lit}`EXISTS` keeps {lit}`acme` and {lit}`NOT EXISTS` keeps
{lit}`zeta`. Native SQLite 3.51.0 gives the same rows. -/
example : (witnessQuery.subqueryRun (Resolved.EvalContext.bound []) partial_.raw
      [.integer 1, .text "acme".toUTF8.toList]).rows ≠ [] ∧
    (witnessQuery.subqueryRun (Resolved.EvalContext.bound []) partial_.raw
      [.integer 2, .text "zeta".toUTF8.toList]).rows = [] := by
  decide +kernel

example : (partial_.run (query existsScript rfl)).returnsResult (· = [[.text "acme".toUTF8.toList]]) ∧
    (partial_.run (query notExistsScript rfl)).returnsResult (· = [[.text "zeta".toUTF8.toList]]) := by
  decide +kernel

#print axioms witness_run
#print axioms witness_empty
#print axioms customersWhere_returns
#print axioms exists_witness
#print axioms not_exists_witness

end SelectSubqueryCases
