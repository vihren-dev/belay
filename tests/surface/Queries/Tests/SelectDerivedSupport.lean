import SelectJoinCases

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Support of the acceptance case A17 of ADR 0027 through the derived source rule
({lit}`Resolved.Query.source_derived`): a derived table, a view and a common table expression
resolve to the same query over subquery 0 of the statement. The result rule of that query takes a
specification of the rows of the inner query and gives the column of each row; the specification
of {lit}`SELECT customer_id, amount FROM orders WHERE amount > 5` over every database with the
catalog of {lit}`orders` serves each of the three forms. -/

namespace SelectDerivedCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases (cell)
open SelectJoinCases (ordersShape orderRows)

/-- The query {lit}`SELECT x.customer_id FROM (inner) x` over subquery 0 of the statement, two
columns wide, whatever the form of the inner query. -/
def derivedQuery : Resolved.Query :=
  { sources := [{ kind := .inner, source := .subquery 0 2, condition := none }], filter := none, aggregate := false,
    groupBy := [], columns := [.scalar (.column 0)], names := ["customer_id"], orderBy := [], offset := 0,
    limit := none }

/-- The condition {lit}`amount > 5` over a row of {lit}`orders`, under integer affinity. -/
def bigCondition : Resolved.Expr := .compare .gt (some .integer) (.column 2) (.literal (.integer 5)) .binary

/-- The inner query {lit}`SELECT customer_id, amount FROM orders WHERE amount > 5`. -/
def bigQuery : Resolved.Query :=
  { sources := [.first 1], filter := some bigCondition, aggregate := false, groupBy := [],
    columns := [.scalar (.column 1), .scalar (.column 2)], names := ["customer_id", "amount"], orderBy := [],
    offset := 0, limit := none }

/-- Whether an order is big: {name}`bigCondition` is true for the order. -/
def Big (order : List Value) : Bool := Resolved.truthy (bigCondition.eval (Resolved.EvalContext.bound []) order)

/-- The specification of {name}`bigQuery`: the {lit}`customer_id` and the {lit}`amount` of each
{name}`Big` order, in scan order. -/
def bigRows (db : Database) : List (List Value) :=
  ((orderRows db).filter Big).map fun order => [cell 1 order, cell 2 order]

/-- For every catalog, database with that catalog and environment, the resolution state of the
connection is that of the catalog. Proof sketch: the state reads only the catalog. -/
theorem catalog_state (catalog db : Database) (env : Env) (schema : db.HasCatalog catalog) :
    (db.raw.connection env.counters).resolveState = (catalog.raw.connection {}).resolveState := by
  simp only [Connection.resolveState, Database.Raw.connection]
  rw [show db.raw.catalog = catalog.raw.catalog from schema]

/-- Inner rule: for every database whose table at position 1 is the table of {lit}`orders` with
the rows of the database, the run of {name}`bigQuery` as subquery 0 of the statement with no
values, for the empty outer row, has the rows {name}`bigRows`, no fault, ends done and has certain
complete rows. Proof sketch: {name}`Resolved.Query.subqueryRun_of_faultless` over the scan of
{lit}`orders`; the query has no window, so its rows are certain
({name}`Resolved.Query.windowCertain_unwindowed`). -/
theorem big_run (db : Database) (orders : db.raw.table 1 = some { shape := ordersShape, rows := db.raw.rows.getD 1 [] }) :
    ((Resolved.EvalContext.statement [] db.raw [bigQuery]).subqueries 0 []).rows = bigRows db ∧
      ((Resolved.EvalContext.statement [] db.raw [bigQuery]).subqueries 0 []).fault = .none ∧
      ((Resolved.EvalContext.statement [] db.raw [bigQuery]).subqueries 0 []).ending = .done ∧
      ((Resolved.EvalContext.statement [] db.raw [bigQuery]).subqueries 0 []).sourceCertain = true := by
  rw [Resolved.EvalContext.statement_subqueries [] db.raw (index := 0) (inner := bigQuery) rfl]
  have run := Resolved.Query.subqueryRun_of_faultless
    (Resolved.subqueryContext 0 {} [] db.raw [bigQuery] none ([bigQuery].length - 1)) db.raw [] none (query := bigQuery)
    rfl rfl rfl
    (Resolved.Query.sourceAfter_first _ db.raw none bigQuery 1 _ [] rfl orders) rfl (by decide +kernel)
    (fun row _ expression member => by
      simp [bigQuery, Resolved.Query.expressions, Resolved.Query.keptExpressions,
        Resolved.QuerySource.expressions, Resolved.QuerySource.first, Resolved.Output.scalars, Resolved.Output.operands] at member
      rcases member with rfl | rfl | rfl <;> rfl)
    (by simp [Resolved.Query.fails, bigQuery]) (by simp [Resolved.Query.distinctCertain, bigQuery])
  rw [run]
  refine ⟨?_, rfl, rfl, by dsimp only; exact Resolved.Query.windowCertain_unwindowed _ rfl _ _⟩
  rw [Resolved.Query.results_plain_unordered _ rfl rfl rfl rfl rfl rfl]
  dsimp only
  generalize Resolved.subqueryContext 0 {} [] db.raw [bigQuery] none ([bigQuery].length - 1) = context
  have output : bigQuery.rowOutput context = fun order => [cell 1 order, cell 2 order] := by
    funext order
    simp [Resolved.Query.rowOutput, bigQuery, Resolved.Expr.eval_column]
  have kept : ∀ rows, Resolved.filtered context bigQuery rows = rows.filter Big := fun rows => by
    simp only [Resolved.filtered, bigQuery]
    rfl
  rw [output, kept]
  simp [bigRows, orderRows, Resolved.outerCells, bigQuery]

/-- Derived result rule: for every catalog, inner query, script that resolves to
{name}`derivedQuery` with the inner query as its one subquery, database with the catalog,
environment, rows {lit}`inner` and property {lit}`Q` of a result: when the statement is calm, the
run of the inner query as subquery 0 of the statement with no values, for the empty outer row,
has the rows {lit}`inner`, no fault, ends done and has certain complete rows, and every
permutation of the first cell of each row of {lit}`inner` has {lit}`Q`, the script returns a
result with {lit}`Q`. Proof sketch: {name}`Resolved.Query.source_derived` gives the source rows,
then {name}`Run.query_returnsResult_faultless` and
{name}`Resolved.Query.perm_of_mem_possibleResults_plain`. -/
theorem derived_returns (catalog : Database) (innerQuery : Resolved.Query) (script : Script)
    (one : script.statements.length = 1) (statement : Syntax.Statement) (head : script.statements = [(statement, [])])
    (resolves : resolveStatement runContext (catalog.raw.connection {}).resolveState statement =
      .ok (.query derivedQuery [innerQuery], (catalog.raw.connection {}).resolveState))
    (calm : (Resolved.Statement.query derivedQuery [innerQuery]).Calm)
    (db : Database) (env : Env) (schema : db.HasCatalog catalog) (inner : List (List Value))
    (rows : ((Resolved.EvalContext.statement [] db.raw [innerQuery]).subqueries 0 []).rows = inner)
    (clean : ((Resolved.EvalContext.statement [] db.raw [innerQuery]).subqueries 0 []).fault = .none)
    (ended : ((Resolved.EvalContext.statement [] db.raw [innerQuery]).subqueries 0 []).ending = .done)
    (certain : ((Resolved.EvalContext.statement [] db.raw [innerQuery]).subqueries 0 []).sourceCertain = true)
    (property : List (List Value) → Prop)
    (holds : ∀ result, result.Perm (inner.map fun row => [cell 0 row]) → property result) :
    (db.run (query script one) env).returnsResult property := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query derivedQuery [innerQuery], (db.raw.connection env.counters).resolveState) := by
    rw [catalog_state catalog db env schema]
    exact resolves
  have found := Resolved.Query.source_derived _ db.raw none derivedQuery 0 2 rfl clean ended certain
  rw [Run.query_returnsResult_faultless head one db env resolved found (by simp) calm rfl
    (Resolved.Query.bindWindow_literal _ _ rfl rfl)
    (fun row _ expression member => by
      simp [derivedQuery, Resolved.Query.expressions, Resolved.Query.keptExpressions,
        Resolved.QuerySource.expressions, Resolved.Output.scalars, Resolved.Output.operands] at member
      subst member
      rfl)
    (by simp [Resolved.Query.fails, derivedQuery]) (by simp [Resolved.Query.distinctCertain, derivedQuery])]
  intro result member
  apply holds
  have perm := Resolved.Query.perm_of_mem_possibleResults_plain rfl rfl rfl rfl rfl member
  have output : derivedQuery.rowOutput (Resolved.EvalContext.statement [] db.raw [innerQuery]) =
      fun row => [cell 0 row] := by
    funext row
    simp [Resolved.Query.rowOutput, derivedQuery, Resolved.Expr.eval_column]
  rwa [Resolved.filtered_of_filter_none _ rfl, output, rows] at perm

#print axioms catalog_state
#print axioms big_run
#print axioms derived_returns

end SelectDerivedCases
