import SuccessBalanceResolveGuard

/-! Subqueries part of the corrected balance example, compiled by the surface success test. -/

set_option doc.verso true
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace BalanceExample

/-- For every simple SELECT 1 query with the given fault-free source and condition, no
fallible call in the condition and no source expressions, the subquery has no fault and returns
one literal row per matching source row.
Proof sketch: apply the shared subquery execution and simple-result equations. -/
theorem one_run (context : Resolved.EvalContext) (database : Model.Database)
    (sources : List Resolved.QuerySource) (condition : Resolved.Expr) (source : Resolved.SourceRows)
    (found : (Resolved.Query.simple sources (some condition) [.scalar (.literal (.integer 1))] ["1"]).source context database = some source)
    (clean : source.fault = .none)
    (sourceQuiet : sources.flatMap Resolved.QuerySource.expressions = [])
    (plain : condition.any Resolved.Expr.isFallibleCall = false)
    (quiet : ∀ row, (condition.evaluate context row).2 = .none) :
    let query := Resolved.Query.simple sources (some condition) [.scalar (.literal (.integer 1))] ["1"]
    (query.subqueryRun context database []).fault = .none ∧
    (query.subqueryRun context database []).rows =
      (source.rows.filter (fun row => Resolved.truthy (condition.eval context row))).map (fun _ => [.integer 1]) := by
  dsimp only
  let query := Resolved.Query.simple sources (some condition) [.scalar (.literal (.integer 1))] ["1"]
  have expressions : query.expressions = [condition, .literal (.integer 1)] := by
    simp [query, Resolved.Query.simple, Resolved.Query.expressions, Resolved.Query.keptExpressions,
      Resolved.Output.scalars, Resolved.Output.operands, sourceQuiet]
  have run := Resolved.Query.subqueryRun_simple context database query
    (Resolved.Query.simple_isSimple _ _ _ _) rfl source found clean
    (by simp [expressions, plain, Resolved.Expr.any, Resolved.Expr.isFallibleCall])
    (by
      intro row member expression inside
      simp only [expressions, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact quiet row
      · rfl)
  constructor
  · rw [run]
  · rw [run]
    have results := (Resolved.Query.simple_isSimple sources (some condition)
      [.scalar (.literal (.integer 1))] ["1"]).results_eq context source.rows
    simpa [query, Resolved.Query.simple, Resolved.filtered, Resolved.Expr.eval_literal] using results

/-- For every context and table found at the given position, the range query has no fault
and returns one row for each cell that fails the SQL range condition.
Proof sketch: Instantiate the SELECT 1 execution law with the table source and range predicate. -/
theorem range_run (context : Resolved.EvalContext) (database : Model.Database)
    (position index : Nat) (table : Table) (cell : CatalogColumn)
    (found : database.table position = some table) :
    ((rangeQuery position index cell).subqueryRun context database []).fault = .none ∧
    ((rangeQuery position index cell).subqueryRun context database []).rows =
      ((Resolved.sourceRows table).filter (fun row => Resolved.truthy ((rangeResolved index cell).eval context row))).map (fun _ => [.integer 1]) := by
  apply one_run (source := {rows := Resolved.sourceRows table, width := table.shape.columns.length, fault := .none})
  · exact Resolved.Query.source_first context _ database position table rfl found
  · rfl
  · rfl
  · simp [rangeResolved, Resolved.Expr.any, Resolved.Expr.isFallibleCall]
  · intro row
    simp [rangeResolved, Resolved.Expr.evaluate, Resolved.Fault.join, Resolved.Fault.soften]

/-- For every context, database and metadata rows, a condition without fallible calls
that has no fault on any row gives a fault-free query with one result per matching metadata row.
Proof sketch: Instantiate the SELECT 1 execution law with fixed pragma rows and the given condition. -/
theorem metadata_run (context : Resolved.EvalContext) (database : Model.Database)
    (rows : List (List Value)) (condition : Resolved.Expr)
    (plain : condition.any Resolved.Expr.isFallibleCall = false)
    (quiet : ∀ row, (condition.evaluate context row).2 = .none) :
    ((metadataQuery rows condition).subqueryRun context database []).fault = .none ∧
    ((metadataQuery rows condition).subqueryRun context database []).rows =
      ((rows.map (· ++ [.text (bytes! "ledger"), .null])).filter
        (fun row => Resolved.truthy (condition.eval context row))).map (fun _ => [.integer 1]) := by
  apply one_run (source := {rows := rows.map (· ++ [.text (bytes! "ledger"), .null]), width := 8, fault := .none})
  · exact Resolved.Query.source_pragma_fixed context _ database 8 _ rfl
  · rfl
  · rfl
  · exact plain
  · exact quiet

/-- For every context and table found at the given position, COUNT returns its source-row
length as a certain singleton result. Apply the COUNT law with the identity filter.
Proof sketch: Apply the COUNT execution law and remove its always-true row filter. -/
theorem count_run (context : Resolved.EvalContext) (database : Model.Database)
    (position : Nat) (table : Table) (found : database.table position = some table) :
    (Resolved.Query.countOf [Resolved.QuerySource.first position] none "count(*)").subqueryRun context database [] =
      Resolved.SubqueryRun.count (Resolved.sourceRows table).length := by
  have count := Resolved.Query.countOf_isCount [Resolved.QuerySource.first position] none "count(*)"
  have run := count.subqueryRun context database rfl _
    (Resolved.Query.source_first context _ database position table rfl found) rfl
    (by simp [Resolved.Query.countOf, Resolved.Query.expressions, Resolved.QuerySource.first,
      Resolved.QuerySource.expressions, Resolved.Query.keptExpressions, Resolved.Output.scalars, Resolved.Output.operands])
    (by simp [Resolved.Query.countOf, Resolved.Query.expressions, Resolved.QuerySource.first,
      Resolved.QuerySource.expressions, Resolved.Query.keptExpressions, Resolved.Output.scalars, Resolved.Output.operands])
  have kept : (Resolved.sourceRows table).filter (fun _ => true) = Resolved.sourceRows table := List.filter_eq_self.mpr (by intros; rfl)
  simpa [Resolved.Query.countOf, Resolved.filtered, Resolved.SubqueryRun.count, kept] using run

end BalanceExample
