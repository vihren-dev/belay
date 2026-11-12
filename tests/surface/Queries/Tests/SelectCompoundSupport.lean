import SelectJoinCases

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Support of the acceptance case A16 of ADR 0027, through the compound rules
({lit}`Run.query_returnsResult_compound`, {lit}`Resolved.Query.perm_of_mem_possibleResults_compound`)
over every database with the catalog of {lit}`shop`: the compound of {lit}`SELECT c.id FROM
customers c` and {lit}`SELECT o.customer_id FROM orders o` gives the rows of its operator
({lit}`CompoundOperator.combine`) over the ids of the customers and the {lit}`customer_id` of the
orders, in some order. {lit}`UNION ALL` keeps both lists with their multiplicity; {lit}`UNION`,
{lit}`INTERSECT` and {lit}`EXCEPT` keep the rows of their membership rules, each once. -/

namespace SelectCompoundCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases (cell)
open SelectJoinCases (shop customerRows orderRows shop_found partial_)

/-- The term {lit}`SELECT t.c FROM t` of a compound over the table at catalog position
{lit}`position`, with the column {lit}`column` of the table, named {lit}`name`. -/
def columnTerm (position column : Nat) (name : String) : Resolved.Query :=
  { sources := [.first position], filter := none, aggregate := false, groupBy := [],
    columns := [.scalar (.column column)], names := [name], orderBy := [], offset := 0, limit := none }

/-- The compound {lit}`SELECT c.id FROM customers c OP SELECT o.customer_id FROM orders o` for the
operator {lit}`OP`: its terms are the subqueries 0 and 1 of the statement. -/
def compoundQuery (operator : CompoundOperator) : Resolved.Query :=
  { sources := [], filter := none, aggregate := false, groupBy := [], columns := [], names := ["id"],
    orderBy := [], offset := 0, limit := none,
    compound := some { first := 0, rest := [(operator, 1)], collations := [.binary] } }

/-- The terms of {name}`compoundQuery`. -/
def terms : List Resolved.Query := [columnTerm 0 0 "id", columnTerm 1 1 "customer_id"]

/-- The ids of the customers, one row for each customer in scan order. -/
def customerIds (db : Database) : List (List Value) := (customerRows db).map fun customer => [cell 0 customer]

/-- The {lit}`customer_id` of the orders, one row for each order in scan order. -/
def orderCustomerIds (db : Database) : List (List Value) := (orderRows db).map fun order => [cell 1 order]

/-- For every context, database, outer row and table at a position of the database, the run of
{name}`columnTerm` for the outer row has the column of each row of the table, in scan order, and
ends done. Proof sketch: {name}`Resolved.Query.subqueryRun_of_faultless`; a column has no fault in
any context, and its value does not read the context ({name}`Resolved.Expr.eval_column`). -/
theorem columnTerm_run (context : Resolved.EvalContext) (database : Model.Database) (outer : List Value)
    {position : Nat} (column : Nat) (name : String) {table : Table} (present : database.table position = some table) :
    ((columnTerm position column name).subqueryRun context database outer).rows =
        (Resolved.sourceRows table).map (fun row => [cell column row]) ∧
      ((columnTerm position column name).subqueryRun context database outer).ending = .done := by
  have run := Resolved.Query.subqueryRun_of_faultless context database outer none
    (query := columnTerm position column name) rfl rfl rfl
    (Resolved.Query.sourceAfter_first _ database none _ position table outer rfl present) rfl
    (by simp [columnTerm, Resolved.Query.expressions, Resolved.Query.keptExpressions, Resolved.QuerySource.expressions,
        Resolved.QuerySource.first, Resolved.Output.scalars, Resolved.Output.operands, Resolved.Expr.any,
        Resolved.Expr.isFallibleCall])
    (fun row _ expression member => by
      simp [columnTerm, Resolved.Query.expressions, Resolved.Query.keptExpressions,
        Resolved.QuerySource.expressions, Resolved.QuerySource.first, Resolved.Output.scalars, Resolved.Output.operands] at member
      subst member
      rfl)
    (by simp [Resolved.Query.fails, columnTerm]) (by simp [Resolved.Query.distinctCertain, columnTerm])
  rw [run]
  refine ⟨?_, rfl⟩
  rw [Resolved.Query.results_plain_unordered _ rfl rfl rfl rfl rfl rfl, Resolved.filtered_of_filter_none _ rfl]
  simp [Resolved.Query.rowOutput, columnTerm, Resolved.outerCells, Resolved.Expr.eval_column]

/-- For every database with the catalog of {name}`shop`, the runs of the two {name}`terms` in the
statement context with no values, for the one source row of the compound, have the
{name}`customerIds` and the {name}`orderCustomerIds` and end done. Proof sketch:
{name}`Resolved.EvalContext.statement_subqueries` and {name}`columnTerm_run`. -/
theorem terms_run (db : Database) (schema : db.HasCatalog shop) :
    ((Resolved.EvalContext.statement [] db.raw terms).subqueries 0 []).rows = customerIds db ∧
      ((Resolved.EvalContext.statement [] db.raw terms).subqueries 0 []).ending = .done ∧
      ((Resolved.EvalContext.statement [] db.raw terms).subqueries 1 []).rows = orderCustomerIds db ∧
      ((Resolved.EvalContext.statement [] db.raw terms).subqueries 1 []).ending = .done := by
  obtain ⟨customers, orders⟩ := shop_found db schema
  rw [Resolved.EvalContext.statement_subqueries [] db.raw (index := 0) (inner := columnTerm 0 0 "id") rfl,
    Resolved.EvalContext.statement_subqueries [] db.raw (index := 1) (inner := columnTerm 1 1 "customer_id") rfl]
  have first := columnTerm_run (Resolved.subqueryContext 0 {} [] db.raw terms none (terms.length - 1)) db.raw [] 0
    "id" (Database.table_of_findTable db.raw _ _ _ customers)
  have second := columnTerm_run (Resolved.subqueryContext 0 {} [] db.raw terms none (terms.length - 1)) db.raw [] 1
    "customer_id" (Database.table_of_findTable db.raw _ _ _ orders)
  exact ⟨first.1, first.2, second.1, second.2⟩

/-- Compound result rule over {name}`shop`: for every operator, script that resolves to
{name}`compoundQuery` with its {name}`terms`, database with the catalog of {name}`shop`,
environment and property {lit}`Q` of a result: when the operator keeps certain rows over the
{name}`customerIds` and the {name}`orderCustomerIds` ({name}`CompoundOperator.keepsCertain`), and
every permutation of the rows of the operator over them ({name}`CompoundOperator.combine`) has
{lit}`Q`, the script returns a result with {lit}`Q`. Proof sketch:
{name}`Run.query_returnsResult_compound` with the term runs of {name}`terms_run`, and
{name}`Resolved.Query.perm_of_mem_possibleResults_compound`. -/
theorem compound_returns (operator : CompoundOperator) (script : Script) (one : script.statements.length = 1)
    (statement : Syntax.Statement) (head : script.statements = [(statement, [])])
    (resolves : resolveStatement runContext (shop.raw.connection {}).resolveState statement =
      .ok (.query (compoundQuery operator) terms, (shop.raw.connection {}).resolveState))
    (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (certain : operator.keepsCertain [.binary] (customerIds db) (orderCustomerIds db) = true)
    (property : List (List Value) → Prop)
    (holds : ∀ result, result.Perm (operator.combine [.binary] (customerIds db) (orderCustomerIds db)) →
      property result) :
    (db.run (query script one) env).returnsResult property := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query (compoundQuery operator) terms, (db.raw.connection env.counters).resolveState) := by
    rw [SelectJoinCases.shop_state db env schema]
    exact resolves
  obtain ⟨firstRows, firstDone, secondRows, secondDone⟩ := terms_run db schema
  have shape : (compoundQuery operator).compound = some { first := 0, rest := [(operator, 1)], collations := [.binary] } :=
    rfl
  rw [Run.query_returnsResult_compound head one db env resolved
    (by unfold Resolved.Statement.Calm; cases operator <;> decide +kernel) shape
    (Resolved.Query.source_none _ _ db.raw rfl) (by simp) rfl
    (by simp [Resolved.Compound.terms, firstDone, secondDone])
    (by simp [Resolved.Compound.combined, firstRows, secondRows, certain])]
  intro result member
  apply holds
  have perm := Resolved.Query.perm_of_mem_possibleResults_compound shape rfl rfl member
  simpa [Resolved.Compound.rows, Resolved.Compound.combined, firstRows, secondRows] using perm

/-- For every operator other than {lit}`UNION ALL`, database and result that is a permutation of
the operator's rows over the {name}`customerIds` and the {name}`orderCustomerIds`, the result has
no duplicate row. Proof sketch: {name}`Resolved.combine_pairwise` and
{name}`Resolved.nodup_of_pairwise_sameOutput`. -/
theorem nodup_of_perm {operator : CompoundOperator} (notAll : operator ≠ .unionAll) (db : Database)
    {result : List (List Value)} (perm : result.Perm (operator.combine [.binary] (customerIds db) (orderCustomerIds db))) :
    result.Nodup :=
  perm.nodup_iff.mpr (Resolved.nodup_of_pairwise_sameOutput (Resolved.combine_pairwise _ notAll _ _))

#print axioms columnTerm_run
#print axioms terms_run
#print axioms compound_returns
#print axioms nodup_of_perm

end SelectCompoundCases
