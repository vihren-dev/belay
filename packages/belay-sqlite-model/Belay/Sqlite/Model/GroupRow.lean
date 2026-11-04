import Belay.Sqlite.Model.QueryEval

set_option doc.verso true

/-! The row of a group of an aggregate query (ADR 0030, D5): the row from which the result
columns, {lit}`HAVING` and {lit}`ORDER BY` read their column references. SQLite's documentation
allows "a single arbitrarily chosen row from within the group" (R-62913-19830); the model gives
the row that SQLite reads when its plan reads the source rows in their order. -/

namespace Belay.Sqlite.Model.Resolved

/-- The row of a group that a deciding call ({lit}`Query.deciding`) gives: for {lit}`min` or
{lit}`max`, the first row whose operand value compares equal to the call's result under the
call's collation, or the last row of the group when the operand is NULL on every row, because
SQLite's {lit}`min` and {lit}`max` load the columns on each NULL row until they have a value.
Any other aggregate gives the first row. For example {lit}`max(n)` over the rows
{lit}`(1.0,'a',1), (1,'A',3)` gives the second row. -/
def Aggregate.decidingRow (context : EvalContext) (group : List (List Value)) : Aggregate → List Value
  | call@(.min operand collation) | call@(.max operand collation) =>
    let best := call.eval context group
    if best.isNull then group.getLastD []
    else (group.find? fun row => collation.compare (operand.eval context row) best == .eq).getD (group.headD [])
  | .countRows | .count _ | .sum _ | .avg _ | .jsonGroupArray .. | .jsonGroupObject .. | .groupConcat ..
  | .total _ => group.headD []

/-- The row of a group from which the expressions of an aggregate query read their column
references: the row of the deciding call ({name}`Aggregate.decidingRow`), or the first row of
the group without one. -/
def Query.groupRow (context : EvalContext) (query : Query) (group : List (List Value)) : List Value :=
  match query.deciding with
  | some call => call.decidingRow context group
  | none => group.headD []

/-- For every query without a deciding call, the row of a group is its first row. Proof sketch:
with {lit}`none` in place of the deciding call, {name}`Query.groupRow` is its first-row branch. -/
@[simp] theorem Query.groupRow_none {context : EvalContext} {query : Query} {group : List (List Value)}
    (none : query.deciding = none) : query.groupRow context group = group.headD [] := by
  simp [Query.groupRow, none]

end Belay.Sqlite.Model.Resolved
