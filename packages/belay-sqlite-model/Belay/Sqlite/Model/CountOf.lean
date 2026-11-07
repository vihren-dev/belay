import Belay.Sqlite.Model.QueryRun

set_option doc.verso true

/-! The count query {lit}`SELECT count(*) FROM t WHERE p` and the number of rows that it counts. The
resolution of {lit}`count(*)` gives {lit}`Resolved.Query.countOf`, and claims about a count compare
{lit}`Resolved.countMatching` with a value. The phase rules give the run of the query
({lit}`Resolved.records_ungrouped`, ADR 0027). -/

namespace Belay.Sqlite.Model

namespace Resolved

/-- The count query of the given sources, {lit}`WHERE` condition and result name: an aggregate query of one
group with the one result column {lit}`count(*)`, and without grouping, ordering, window, {lit}`HAVING`,
{lit}`DISTINCT` or compound, that reads no cell of an outer query. -/
def Query.countOf (sources : List QuerySource) (filter : Option Expr) (name : String) : Query :=
  { sources, filter, aggregate := true, groupBy := [], columns := [.aggregate .countRows], names := [name],
    orderBy := [], offset := 0, limit := none, limitParameter := none, offsetParameter := none, outer := 0,
    aggregates := [], having := none, distinct := none }

end Resolved

/-- The result of a subquery that gives one row with the integer {lit}`count`, no fault and certain rows, as
{lit}`SELECT count(*) FROM t` does. -/
def Resolved.SubqueryRun.count (count : Nat) : Resolved.SubqueryRun :=
  { rows := [[.integer count]], fault := .none }

/-- The number of rows of a table for which a condition is true in a context, in scan order: all the rows when
there is no condition. For example, with the condition {lit}`x > 1` it counts the rows whose {lit}`x` is greater
than one; a row for which the condition is NULL is not counted. -/
def Resolved.countMatching (context : Resolved.EvalContext) (condition : Option Resolved.Expr) (table : Table) : Nat :=
  ((Resolved.sourceRows table).filter fun row => condition.all fun expression =>
    Resolved.truthy (expression.eval context row)).length

/-- For every sources, condition and result name, the expressions of the count query are the condition, if
any, then the expressions of the sources ({name}`Resolved.QuerySource.expressions`): {lit}`count(*)` has no
operand. Proof sketch: the definitions compute. -/
theorem Resolved.Query.countOf_expressions (sources : List Resolved.QuerySource) (condition : Option Resolved.Expr)
    (name : String) :
    (Resolved.Query.countOf sources condition name).expressions =
      condition.toList ++ sources.flatMap Resolved.QuerySource.expressions := by
  simp [Resolved.Query.expressions, Resolved.Query.keptExpressions, Resolved.Query.countOf, Resolved.Output.scalars,
    Resolved.Output.operands]

end Belay.Sqlite.Model
