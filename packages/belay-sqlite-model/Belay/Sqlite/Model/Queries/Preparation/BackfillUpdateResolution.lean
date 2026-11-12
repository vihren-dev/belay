import Belay.Sqlite.Model.Queries.Preparation.ColumnPositionAppend
import Belay.Sqlite.Model.Queries.Select.ExprResolutionLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every one-table scope and written identifier that names a column of the table, the identifier
mentions a column of the scope ({name}`mentionsColumn`). In plain words, a written value that uses a
column of the table depends on the row. The result is the same whether the table has an alias or a
catalog position. Proof sketch: the scope has the table as its one visible source, and the column is
found in it, so the matching positions are not empty. -/
theorem mentionsColumn_identifier_singleAt {position : Option Nat} {tableName name : Identifier}
    {columns : List CatalogColumn} {rowid aliased : Bool} {index : Nat} (quote : Syntax.QuoteKind)
    (found : columnPosition columns name = some index) :
    mentionsColumn (Scope.singleAt position tableName columns rowid aliased) (.identifier name quote) = true := by
  simp [mentionsColumn, Scope.matches, Scope.singleAt, found]

/-- For every scope, position, written expression that mentions a column of the scope, and resolved
expression: the resolved value of the assignment ({name}`assignedExpression`) is the resolved expression
itself. In plain words, a backfill from an expression of the row's cells assigns that expression, not a
constant. Proof sketch: the definition takes the first branch when the expression mentions a column. -/
theorem assignedExpression_of_mentions {scope : Scope} {position : Nat} {expression : Syntax.Expr}
    {resolved : Resolved.Expr} (mentions : mentionsColumn scope expression = true) :
    assignedExpression scope position expression resolved = resolved := by
  simp [assignedExpression, mentions]

/-- For every scope, position, expression and resolved expression, if the resolved expression reads only
columns below a width, so does the resolved value of an assignment ({name}`assignedExpression`): it is
that expression, or the literal of its stored value. Proof sketch: a literal reads no column. -/
theorem assignedExpression_readsBelow {scope : Scope} {position : Nat} {expression : Syntax.Expr}
    {resolved : Resolved.Expr} {width : Nat} (below : resolved.readsBelow width = true) :
    (assignedExpression scope position expression resolved).readsBelow width = true := by
  unfold assignedExpression
  split
  · exact below
  · simp [Resolved.Expr.readsBelow, Resolved.Expr.any, Resolved.Expr.isColumnFrom]

end Belay.Sqlite.Model
