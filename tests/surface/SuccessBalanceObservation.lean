import SuccessBalanceSubqueries

/-! Observation part of the corrected balance example, compiled by the surface success test. -/

set_option doc.verso true
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace BalanceExample

/-- For every context whose four subqueries are the given fault-free runs and COUNT,
the outer condition has no fault. It is true exactly when the range result is empty, the count
is below one million, and both metadata results are nonempty.
Proof sketch: reduce EXISTS, the scalar COUNT comparison and the conjunction. -/
theorem guard_from_runs (context : Resolved.EvalContext)
    (range account typed : Resolved.SubqueryRun) (count : Nat)
    (atRange : context.subqueries 0 [] = range)
    (atCount : context.subqueries 1 [] = Resolved.SubqueryRun.count count)
    (atAccount : context.subqueries 2 [] = account)
    (atTyped : context.subqueries 3 [] = typed)
    (rangeQuiet : range.fault = .none)
    (accountQuiet : account.fault = .none)
    (typedQuiet : typed.fault = .none) :
    (guardCondition.evaluate context []).2 = .none ∧
    (Resolved.truthy (guardCondition.eval context []) = true ↔
      range.rows = [] ∧ count < 1000000 ∧ account.rows ≠ [] ∧ typed.rows ≠ []) := by
  constructor
  · simp [guardCondition, Resolved.Expr.evaluate, atRange, atCount, atAccount, atTyped,
      rangeQuiet, accountQuiet, typedQuiet, Resolved.SubqueryRun.count,
      Resolved.Fault.join, Resolved.Fault.soften]
  · have compared : ((compare (count : Int) 1000000) == Ordering.lt) = decide (count < 1000000) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, Int.compare_eq_lt, decide_eq_true_eq]
      omega
    simp only [guardCondition, Resolved.Expr.eval_and, Resolved.truthy_and, Resolved.Expr.eval_not,
      Resolved.truthy_not, Resolved.Expr.eval_exists, Resolved.Expr.eval_compare, Resolved.Expr.eval_subquery,
      Resolved.Expr.eval_literal, atRange, atCount, atAccount, atTyped, Resolved.SubqueryRun.count,
      List.head?_cons, Option.bind_some, Option.getD_some, Resolved.comparisonOperands,
      Comparison.apply, Value.isNull, Bool.false_or, Bool.false_eq_true, ite_false,
      Collation.compare_integer, Comparison.holds, compared, truthy_truth,
      Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, decide_eq_true_eq]
    cases empty : range.rows.isEmpty <;> simp [Resolved.falsy, truth, Value.isNull, Resolved.truthy, and_assoc] <;> simp_all

/-- For every clock, counters, parameters, database and found table, the guard at positive
subquery depth has no fault. Its truth is exactly the four filtered-row facts at the inner depth.
Proof sketch: instantiate each subquery run and substitute them into the conjunction law. -/
theorem guard_context (clock : Int) (counters : Counters) (parameters : List Value)
    (database : Model.Database) (position index : Nat) (table : Table) (cell : CatalogColumn)
    (depth : Nat) (found : database.table position = some table) :
    let queries := guardQueries position index table.shape cell
    let context := Resolved.subqueryContext clock counters parameters database queries none (depth + 1)
    let inner := Resolved.subqueryContext clock counters parameters database queries none depth
    (guardCondition.evaluate context []).2 = .none ∧
      (Resolved.truthy (guardCondition.eval context []) = true ↔
        filteredOnes inner (rangeResolved index cell) (Resolved.sourceRows table) = [] ∧
        (Resolved.sourceRows table).length < 1000000 ∧
        filteredOnes inner (nameResolved (bytes! "account")) (table.shape.infoRows.map (· ++ [.text (bytes! "ledger"), .null])) ≠ [] ∧
        filteredOnes inner typedResolved (table.shape.infoRows.map (· ++ [.text (bytes! "ledger"), .null])) ≠ []) := by
  dsimp only
  let queries := guardQueries position index table.shape cell
  let inner := Resolved.subqueryContext clock counters parameters database queries none depth
  let context := Resolved.subqueryContext clock counters parameters database queries none (depth + 1)
  have range := range_run inner database position index table cell found
  have account := metadata_run inner database table.shape.infoRows (nameResolved (bytes! "account"))
    (by simp [nameResolved, Resolved.Expr.any, Resolved.Expr.isFallibleCall])
    (by intro row; simp [nameResolved, Resolved.Expr.evaluate, Resolved.Fault.join, Resolved.Fault.soften])
  have typed := metadata_run inner database table.shape.infoRows typedResolved
    (by simp [typedResolved, nameResolved, Resolved.Expr.any, Resolved.Expr.isFallibleCall])
    (by intro row; simp [typedResolved, nameResolved, Resolved.Expr.evaluate, Resolved.Fault.join, Resolved.Fault.soften])
  have guard := guard_from_runs context
    ((rangeQuery position index cell).subqueryRun inner database [])
    ((metadataQuery table.shape.infoRows (nameResolved (bytes! "account"))).subqueryRun inner database [])
    ((metadataQuery table.shape.infoRows typedResolved).subqueryRun inner database [])
    (Resolved.sourceRows table).length rfl
    (by exact count_run inner database position table found) rfl rfl range.1 account.1 typed.1
  simpa only [range.2, account.2, typed.2, filteredOnes] using guard

/-- For every table, positions and column, the resolved guard reads no clock or counter.
Proof sketch: Expand the four query expressions; none reads the environment. -/
theorem guard_calm (position index : Nat) (table : CatalogTable) (cell : CatalogColumn) :
    (Resolved.Statement.query (Resolved.Query.selectOneWhere guardCondition) (guardQueries position index table cell)).Calm := by
  simp [Resolved.Statement.Calm, Resolved.Statement.clockExpressions, guardQueries,
    Resolved.Query.selectOneWhere, rangeQuery, metadataQuery, Resolved.Query.simple, Resolved.Query.countOf,
    Resolved.Query.expressions, Resolved.QuerySource.expressions, Resolved.Query.keptExpressions,
    Resolved.Output.scalars, Resolved.Output.operands, Resolved.QuerySource.first, Resolved.QuerySource.pragma,
    Resolved.Expr.Calm, guardCondition, rangeResolved, nameResolved, typedResolved, Resolved.Expr.any,
    Resolved.Expr.isFallibleCall, Resolved.Expr.readsClockHere, Resolved.Expr.readsCounterHere]

/-- For every database with the ledger, cents column and unshadowed pragma, the guard
statement resolves to its query and keeps the resolution state.
Proof sketch: Lift complete query resolution through the statement wrapper. -/
theorem guard_statement (db : Database) (position index : Nat) (table : CatalogTable) (cell : CatalogColumn)
    (found : db.raw.catalog.findTable ledgerRef.table = some (position, table))
    (notTable : db.raw.catalog.findTable pragmaRef.table = none)
    (notView : db.raw.catalog.findView pragmaRef.table = none)
    (column : columnPosition table.columns (name! "cents") = some index)
    (atIndex : table.columns[index]? = some cell) :
    resolveStatement runContext db.raw.connection.resolveState balanceGuard.statements[0].1 =
      .ok (.query (Resolved.Query.selectOneWhere guardCondition) (guardQueries position index table cell),
        db.raw.connection.resolveState) := by
  exact resolveStatement_select_of_resolveSelect runContext db.raw.connection.resolveState mainSyntax balanceQueries rfl rfl _
    (guard_select db.raw.catalog position index table cell found notTable notView column atIndex)

/-- For every database with the ledger, cents column and unshadowed pragma, there is an
inner evaluation context in which Holds of the guard means: no bad-range result, fewer than
one million source rows, an account-name result and an INTEGER-declared cents result.
Proof sketch: the statement is calm and fault-free; the query output bridge reduces Holds
to the truth of the outer conjunction. -/
theorem guard_holds (db : Database) (position index : Nat) (table : CatalogTable) (cell : CatalogColumn)
    (found : db.raw.catalog.findTable ledgerRef.table = some (position, table))
    (notTable : db.raw.catalog.findTable pragmaRef.table = none)
    (notView : db.raw.catalog.findView pragmaRef.table = none)
    (column : columnPosition table.columns (name! "cents") = some index)
    (atIndex : table.columns[index]? = some cell) :
    ∃ inner : Resolved.EvalContext, Holds balanceGuard db ↔
        filteredOnes inner (rangeResolved index cell) (Resolved.sourceRows {shape := table, rows := db.raw.rows.getD position []}) = [] ∧
        (Resolved.sourceRows {shape := table, rows := db.raw.rows.getD position []}).length < 1000000 ∧
        filteredOnes inner (nameResolved (bytes! "account")) (table.infoRows.map (· ++ [.text (bytes! "ledger"), .null])) ≠ [] ∧
        filteredOnes inner typedResolved (table.infoRows.map (· ++ [.text (bytes! "ledger"), .null])) ≠ [] := by
  let query := Resolved.Query.selectOneWhere guardCondition
  let queries := guardQueries position index table cell
  let counters := db.raw.connection.state.counters.view (Resolved.Statement.query query queries).counterReads
  let inner := Resolved.subqueryContext 0 counters [] db.raw queries none 3
  have ran := guard_context 0 counters [] db.raw position index
    {shape := table, rows := db.raw.rows.getD position []} cell 3 (db.raw.table_of_findTable _ _ _ found)
  have faultless := Resolved.Query.selectOneWhere_faultless
    (db.raw.connection.queryContext [] query queries) guardCondition ran.1
  have output := Script.outputOn_query balanceGuard db _ [] [] query queries _ rfl
    (guard_statement db position index table cell found notTable notView column atIndex)
  refine ⟨inner, ?_⟩
  unfold Holds
  rw [output, Option.any_some, resolvedStepOutput_noFrom_hasRows 0 db.raw.connection []
    (some guardCondition) [.scalar (.literal (.integer 1))] ["1"] queries (guard_calm _ _ _ _) faultless]
  exact ran.2

end BalanceExample
