import Belay.Sqlite.Model.Queries.Select.GeneratedColumns
import Belay.Sqlite.Model.Shared.Resolved.Context

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Whether a column name of a text is exactly the declared name of the column that it finds: the same
bytes and no double quote. A name that finds no column is exact, because it is no reference to a column. -/
def spelledAsDeclared (columns : List CatalogColumn) (name : Identifier) (quote : Syntax.QuoteKind) : Bool :=
  quote != .double && match columnPosition columns name with
    | some position => (columns[position]?.map (·.name == name)).getD false
    | none => true

mutual
/-- Whether every column name of an expression is spelled as the column is declared
({name}`spelledAsDeclared`). A qualified name, a subquery and a RAISE are not exact, because the error
of SQLite prints more than the column name for them. -/
def Syntax.Expr.spelledAsDeclared (columns : List CatalogColumn) : Syntax.Expr → Bool
  | .identifier name quote => Belay.Sqlite.Model.spelledAsDeclared columns name quote
  | .qualified .. | .exists _ | .subquery _ | .inQuery .. | .raise .. => false
  | .compare _ left right | .and left right | .or left right | .arithmetic _ left right | .concatenate left right =>
    left.spelledAsDeclared columns && right.spelledAsDeclared columns
  | .not operand | .isNull operand _ | .negate operand | .positive operand | .cast operand _ | .collate operand _ =>
    operand.spelledAsDeclared columns
  | .call _ arguments => Syntax.Expr.allSpelledAsDeclared columns arguments
  | .inList operand values _ =>
    operand.spelledAsDeclared columns && Syntax.Expr.allSpelledAsDeclared columns values
  | .between operand low high _ =>
    operand.spelledAsDeclared columns && low.spelledAsDeclared columns && high.spelledAsDeclared columns
  | .caseOf operands _ => Syntax.Expr.allSpelledAsDeclared columns operands
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .callStar _ => true

/-- Whether every expression of the list is spelled as the columns are declared. -/
def Syntax.Expr.allSpelledAsDeclared (columns : List CatalogColumn) : List Syntax.Expr → Bool
  | [] => true
  | argument :: rest => argument.spelledAsDeclared columns && Syntax.Expr.allSpelledAsDeclared columns rest
end

/-- Whether the key terms and the filter of an index are spelled as the columns of its table are
declared. -/
def indexSpelledAsDeclared (columns : List CatalogColumn) (terms : List Syntax.OrderTerm)
    (filter : Option Syntax.Expr) : Bool :=
  terms.all (·.expression.spelledAsDeclared columns) && (filter.map (·.spelledAsDeclared columns)).getD true

end Belay.Sqlite.Model
