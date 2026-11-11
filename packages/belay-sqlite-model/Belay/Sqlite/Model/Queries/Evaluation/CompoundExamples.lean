import Belay.Sqlite.Model.Shared.Execution.Execution

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved.CompoundExamples

/-- {lit}`SELECT values`, a term without {lit}`FROM`. -/
def literals (values : List Expr) : Query where
  sources := []
  filter := none
  aggregate := false
  groupBy := []
  columns := values.map .scalar
  names := values.map fun _ => "x"
  orderBy := []
  offset := 0
  limit := none

/-- The integer literal {lit}`n`. -/
def int (n : Int) : Expr := .literal (.integer n)

/-- {lit}`abs(-9223372036854775808)`, which fails with {lit}`integer overflow`. -/
def failing : Expr := .scalar .abs (.cons (int (-9223372036854775808)) .nil)

/-- A compound query over the terms at indexes 0 to n in order, with the operators between
them and one collation for each column. -/
def compound (operators : List CompoundOperator) (collations : List Collation) : Query :=
  let rest := operators.zipIdx.map fun (operator, index) => (operator, index + 1)
  { literals [] with names := collations.map fun _ => "x", compound := some { first := 0, rest, collations } }

end Belay.Sqlite.Model.Resolved.CompoundExamples
