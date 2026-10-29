import Belay.Sqlite.Model.NoFromQuerySteps
import Belay.Sqlite.Model.SimpleSubqueryRowsOutput

set_option doc.verso true

/-! The complete result of a fault-free condition in a calm SELECT 1 statement. -/

namespace Belay.Sqlite.Model

/-- For every calm SELECT 1 statement whose condition has no fault on the empty row,
the complete output is the singleton row containing integer one when the condition is true,
and no rows otherwise. Subquery results need not have a certain first row unless the condition
reads it. Proof sketch: the source is one empty row, and the simple result filters that row. -/
theorem resolvedStepOutput_selectOne (index : Nat) (connection : Connection) (parameters : List Value)
    (condition : Resolved.Expr) (subqueries : List Resolved.Query)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere condition) subqueries).Calm)
    (faultless : (condition.evaluate
      (connection.queryContext parameters (Resolved.Query.selectOneWhere condition) subqueries) []).2 = .none) :
    resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere condition) subqueries) =
      .rows (if Resolved.truthy (condition.eval
        (connection.queryContext parameters (Resolved.Query.selectOneWhere condition) subqueries) []) then
          [[.integer 1]] else []) := by
  rw [resolvedStepOutput_simple_rows_of_faultless none index connection parameters _ subqueries
    (Resolved.Query.simple_isSimple _ _ _ _) { rows := [[]], width := 0, fault := .none } calm
    (Resolved.Query.source_none _ _ _ rfl) rfl (fun row member expression inside => by
      have empty : row = [] := by simpa using member
      subst row
      exact Resolved.Query.selectOneWhere_faultless _ _ faultless expression inside),
    Resolved.Query.Simple.results_eq (Resolved.Query.simple_isSimple _ _ _ _)]
  simp only [Resolved.filtered, Resolved.Query.selectOneWhere, Resolved.Query.simple, Option.all_some]
  simp only [List.filter_cons, List.filter_nil]
  split <;> simp_all [Resolved.normalForm, Resolved.stableSort, Resolved.insertStable,
    Resolved.Expr.eval, Resolved.Expr.evaluate]

end Belay.Sqlite.Model
