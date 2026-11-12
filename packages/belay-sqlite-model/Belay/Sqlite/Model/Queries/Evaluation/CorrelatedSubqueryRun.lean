import Belay.Sqlite.Model.Queries.Evaluation.CorrelatedSubquerySource
import Belay.Sqlite.Model.Queries.Evaluation.SelectSubqueryRules

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- Whether an optional {lit}`WHERE` expression keeps a row in a context: there is no expression, or the expression is
true for the row. It is the test of {name}`filtered`. -/
def conditionKeeps (condition : Option Expr) (context : EvalContext) (row : List Value) : Bool :=
  condition.all fun expression => truthy (expression.eval context row)

/-- The simple subquery of one table at a position: its only source is the table, it has the optional {lit}`WHERE`
expression, and its result columns are the given expressions. The rows of the outer query have {lit}`outer` cells, and
they come first in a row of the subquery, so the cells of the table start at position {lit}`outer`. With the width
{lit}`outer = 0` it is a top-level query of one table. -/
def Query.oneTable (table outer : Nat) (condition : Option Expr) (projections : List Expr) (names : List String) :
    Query :=
  { Query.simple [QuerySource.first table] condition (projections.map .scalar) names with outer }

/-- The expressions of the query {name}`Query.oneTable` are its condition and its result expressions. Proof sketch:
unfold the expressions of the query; the one source has no condition and no argument. -/
theorem Query.oneTable_expressions (table outer : Nat) (condition : Option Expr) (projections : List Expr)
    (names : List String) :
    (Query.oneTable table outer condition projections names).expressions = condition.toList ++ projections := by
  simp [Query.oneTable, Query.simple, Query.expressions, Query.keptExpressions, Output.scalars, Output.operands,
    QuerySource.expressions, QuerySource.first, List.flatMap_map]

end Belay.Sqlite.Model.Resolved
