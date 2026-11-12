import Belay.Sqlite.Model.Queries.Evaluation.InSubqueryEqualityLink
import Belay.Sqlite.Model.Queries.Evaluation.SelectOneSubqueryContext

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every statement of {name}`Resolved.Query.oneTable` with one subquery, the statement is calm
({name}`Resolved.Statement.Calm`) when its condition, its result expressions and the expressions of the subquery are
calm ({name}`Resolved.Expr.Calm`). Proof sketch: the expressions of the statement are the condition, the result
expressions and the expressions of the subquery. -/
theorem Resolved.Query.oneTable_calm (position : Nat) (condition : Option Resolved.Expr)
    (projections : List Resolved.Expr) (names : List String) (inner : Resolved.Query)
    (conditionCalm : ∀ expression ∈ condition.toList, expression.Calm)
    (projectionsCalm : ∀ expression ∈ projections, expression.Calm)
    (innerCalm : ∀ expression ∈ inner.expressions, expression.Calm) :
    (Resolved.Statement.query (Resolved.Query.oneTable position 0 condition projections names) [inner]).Calm := by
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.oneTable_expressions, List.mem_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil] at member
  rcases member with (member | member) | member
  · exact conditionCalm expression member
  · exact projectionsCalm expression member
  · exact innerCalm expression member

end Belay.Sqlite.Model
