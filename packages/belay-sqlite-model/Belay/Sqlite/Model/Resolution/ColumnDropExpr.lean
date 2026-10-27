import Belay.Sqlite.Model.Resolution.ExprAny

set_option doc.verso true

/-! The positions of columns after ALTER TABLE DROP COLUMN. The cells after the dropped column move down
by one, so a resolved expression that reads a column after it reads the column one place lower. An
expression that reads the dropped column itself has no such place; {lit}`ColumnDropCatalog.lean` accepts
the drop only when no expression of the table reads it. -/

namespace Belay.Sqlite.Model

/-- The position of a column after the column at {lit}`index` was dropped: a column before it keeps its
position, and a column after it moves down by one. The dropped column has no position; this function gives
it the position before it, and the callers exclude it. -/
def dropPosition (index position : Nat) : Nat := if position < index then position else position - 1

end Belay.Sqlite.Model

namespace Belay.Sqlite.Model.Resolved

mutual
/-- The expression with every column position changed for the drop of the column at {lit}`index`
({lit}`dropPosition`). The subquery numbers and the other parts stay. -/
def Expr.dropColumn (index : Nat) : Expr → Expr
  | .column position => .column (dropPosition index position)
  | .literal value => .literal value
  | .compare operator affinity left right collation =>
    .compare operator affinity (left.dropColumn index) (right.dropColumn index) collation
  | .and left right => .and (left.dropColumn index) (right.dropColumn index)
  | .or left right => .or (left.dropColumn index) (right.dropColumn index)
  | .not operand => .not (operand.dropColumn index)
  | .isNull operand negated => .isNull (operand.dropColumn index) negated
  | .arithmetic operator left right => .arithmetic operator (left.dropColumn index) (right.dropColumn index)
  | .cast affinity operand => .cast affinity (operand.dropColumn index)
  | .coalesce first rest => .coalesce (first.dropColumn index) (rest.dropColumn index)
  | .json function arguments => .json function (arguments.dropColumn index)
  | .now keyword => .now keyword
  | .parameter number => .parameter number
  | .counter kind => .counter kind
  | .date function arguments => .date function (arguments.dropColumn index)
  | .scalar function arguments => .scalar function (arguments.dropColumn index)
  | .exists subquery => .exists subquery
  | .inQuery operand subquery affinity collation negated =>
    .inQuery (operand.dropColumn index) subquery affinity collation negated
  | .subquery number => .subquery number
  | .inList operand values affinity collation negated =>
    .inList (operand.dropColumn index) (values.dropColumn index) affinity collation negated
  | .aggregateValue number => .aggregateValue number

/-- The arguments with every column position changed for the drop of the column at {lit}`index`. -/
def Arguments.dropColumn (index : Nat) : Arguments → Arguments
  | .nil => .nil
  | .cons head tail => .cons (head.dropColumn index) (tail.dropColumn index)
end

end Belay.Sqlite.Model.Resolved
