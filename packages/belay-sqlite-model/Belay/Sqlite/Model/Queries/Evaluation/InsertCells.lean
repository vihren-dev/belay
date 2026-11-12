import Belay.Sqlite.Model.Queries.Select.Defaults
import Belay.Sqlite.Model.Queries.Preparation.Assignments

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- One {lit}`VALUES` item, a constant expression of a write (ADR 0012, slices 3a and
6e2): the expression resolved as a query expression with no column in scope and an
aggregate as SQLite's {lit}`misuse of aggregate function`. Its value, so {lit}`1 + 2` is 3
and {lit}`CAST('7' AS INTEGER)` is 7, computed at the clock value 0, which it does not
read; or the expression when it reads the clock or a parameter, or names a subquery of the statement
({lit}`shapes`, {lit}`Resolved.Expr.namesSubquery`). An identifier, a rowid name included, is
a double-quoted string or {lit}`no such column`, as no table is in scope. A value whose
JSON function may fail is a model restriction, because the model does not describe when
SQLite evaluates a constant. The value is not yet stored with the column's affinity
({lit}`fullCells` stores it). In a trigger's body, {lit}`scope` has the trigger's rows (ADR
0018, D5), and an item that names them stays an expression too; elsewhere it is empty. The
trace holds the names of the item, with paths relative to the item. -/
def constantCellTraced (dqs : Bool) (shapes : SubqueryShapes) (expression : Syntax.Expr) (scope : Scope := []) :
    Traced ValueIssue Resolved.Cell := do
  let operand ← resolveOperandTraced dqs scope shapes true expression
  if operand.1.readsClock || operand.1.readsRunValue || operand.1.any Resolved.Expr.namesSubquery ||
      mentionsColumn scope expression then
    if operand.1.any Resolved.Expr.isFallibleCall then throw (.restriction [] .constantFunctionError)
    else pure (.expression operand.1)
  else if operand.1.mayFailOn (.plain 0) [] then throw (.restriction [] .constantFunctionError)
  else pure (.value (operand.1.eval (.plain 0) []))

end Belay.Sqlite.Model
