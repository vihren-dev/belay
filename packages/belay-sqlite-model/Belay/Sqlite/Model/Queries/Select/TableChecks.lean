import Belay.Sqlite.Model.Queries.Select.ParameterOrder

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The model restriction of a resolved CHECK condition, or none: a time keyword or a date
and time function, which can give another value on each evaluation, a call of a connection counter
({name}`Resolved.Expr.isCounter`), whose value depends on the statements that ran before, and a JSON function
or another function whose evaluation can fail ({name}`Resolved.Expr.isFallibleCall`), are {name}`RestrictionKind.checkFunction`. -/
def checkIssue (resolved : Resolved.Expr) : Option ValueIssue :=
  if resolved.any Resolved.Expr.isNow || resolved.any Resolved.Expr.isDateCall ||
      resolved.any Resolved.Expr.isCounter ||
      resolved.any Resolved.Expr.isFallibleCall then some (.restriction [] .checkFunction)
  else none

/-- What the resolver decided a name of the text of a CHECK constraint stands for, from the occurrences of the
condition: a column that it found in the table, or a qualifier that it resolved to a source; none for another
name, such as a double-quoted string. -/
def NameOccurrence.labelTarget? (occurrence : NameOccurrence) : Option LabelTarget :=
  match occurrence.role with
  | .columnReference => match occurrence.result with
    | .found [binding] => some (.column binding.column.index)
    | .found _ | .ambiguous _ | .missing .. | .source _ | .schema _ | .resultColumn _ | .declares | .compared ..
    | .unreached _ => none
  | .qualifier => match occurrence.result with
    | .source _ => some .table
    | .found _ | .ambiguous _ | .missing .. | .schema _ | .resultColumn _ | .declares | .compared ..
    | .unreached _ => none
  | .columnTarget | .tableReference | .aliasDeclaration | .resultAlias | .comparisonSite => none

/-- The name tokens of the text of a CHECK constraint that the resolver bound to the table or to a column,
by the node paths of the tokens and the occurrences of the condition ({name}`resolveOperandTraced`): no
second lookup of a spelling. -/
def checkText (dqs : Bool) (scope : Scope) (condition : Syntax.Expr) (text : Syntax.SourceText) : Option CheckText :=
  if text.text.isEmpty then none else
  let occurrences := (resolveOperandTraced dqs scope {} true condition).trace
  some { text := text.text, names := text.tokens.filterMap fun token =>
    (occurrences.findSome? fun occurrence =>
      if token.paths.contains occurrence.path then occurrence.labelTarget? else none).map fun target =>
      { start := token.start, stop := token.stop, quote := token.quote, target } }

/-- One CHECK constraint over the scope of its table: the condition, its label and the tokens of its text
({name}`checkText`). A parameter is {name}`ExprError.parameterInCheck`, in SQLite's order
({name}`prohibitParameter`). -/
def resolveCheck (dqs : Bool) (scope : Scope) (condition : Syntax.Expr) (label : String)
    (text : Syntax.SourceText := {}) : Except ValueIssue CheckConstraint := do
  prohibitParameter dqs scope .parameterInCheck condition
  let resolved ← Belay.Sqlite.Model.condition [] (resolveOperand dqs scope {} true condition)
  match checkIssue resolved with
  | some issue => .error issue
  | none => .ok { condition := resolved, label, source := checkText dqs scope condition text }

end Belay.Sqlite.Model
