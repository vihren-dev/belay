import Belay.Sqlite.Model.SelectOneOutput
import Belay.Sqlite.Model.ExistsSubqueryOutput

set_option doc.verso true

/-! The output of {lit}`SELECT 1 WHERE NOT EXISTS (SELECT … FROM t WHERE p)` (ADR 0017, S4): the
statement of {lit}`ExistsSubqueryOutput` with {lit}`NOT`. It has rows exactly when {lit}`p` is true for no
row of the table, has no rows exactly when it is true for some row, and is never an error. -/

namespace Belay.Sqlite.Model

/-- For every calm SELECT 1 statement with a simple EXISTS subquery over an existing table,
the complete output contains integer one when no source row matches, and is empty otherwise.
Proof sketch: substitute the subquery run; its result is empty exactly when no row passes its filter. -/
theorem resolvedStepOutput_notExists (index position : Nat) (connection : Connection) (parameters : List Value)
    (table : Table) (condition : Option Resolved.Expr) (columns : List Resolved.Output) (names : List String)
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere (.not (.exists 0)))
      [Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names]).Calm) :
    resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere (.not (.exists 0)))
      [Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names]) =
      .rows (if !(Resolved.sourceRows table).any (fun row => condition.all
        (fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row)))
        then [[.integer 1]] else []) := by
  have run := connection.queryContext_tableSubquery_zero parameters _ position table condition columns names present calm
  rw [resolvedStepOutput_selectOne index connection parameters _ _ calm
    (by rw [Resolved.Expr.fault_not, Resolved.Expr.fault_exists, run])]
  simp only [Resolved.Expr.eval_not, Resolved.truthy_not, Resolved.Expr.eval_exists, run, truthy_truth, Resolved.falsy, isNull_truth, Bool.not_false, Bool.true_and, Bool.not_not]
  have empty := (Resolved.Query.simple_isSimple [Resolved.QuerySource.first position] condition columns names).results_eq_nil_iff
    (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table)
  have same : ((Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names).results
      (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table)).isEmpty =
      !(Resolved.sourceRows table).any (fun row => condition.all
        (fun expression => Resolved.truthy (expression.eval (Resolved.EvalContext.bound parameters) row))) := by
    apply Bool.eq_iff_iff.mpr
    simpa [List.isEmpty_iff, Bool.not_eq_true', List.any_eq_false, Resolved.Query.simple] using empty
  rw [same]

end Belay.Sqlite.Model
