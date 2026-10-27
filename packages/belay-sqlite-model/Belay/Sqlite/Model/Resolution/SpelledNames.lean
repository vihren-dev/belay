import Belay.Sqlite.Model.Resolution.SyntaxScope
import Belay.Sqlite.Model.Resolution.GeneratedColumns
import Belay.Sqlite.Model.Resolution.Context

set_option doc.verso true

/-! How the text of a definition spells the columns that it names. SQLite keeps the text of a table and of
an index, and prints a name of it as written when the text no longer resolves, for example after a
column was dropped ({lit}`error in table t after drop column: no such column: b`). The model keeps no text
for generated columns, table-level keys, foreign keys and indexes, so it records whether the text spelled
every column name as the column is declared ({lit}`CatalogTable.exactNames`,
{lit}`CatalogIndex.exactNames`). A name with a double quote is not exact, because SQLite adds a hint about
string literals to its error for such a name. -/

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

/-- Whether the column names of the table-level UNIQUE constraints and FOREIGN KEY constraints of a
definition are spelled as the columns are declared. A PRIMARY KEY constraint needs no spelling, because the
error of SQLite for a dropped key column prints the name of the statement. -/
def Syntax.TableConstraint.spelledAsDeclared (columns : List CatalogColumn) : Syntax.TableConstraint → Bool
  | .unique names _ | .foreignKey names .. =>
    names.all fun name => Belay.Sqlite.Model.spelledAsDeclared columns name .none
  | .primaryKey .. | .check .. | .deferral _ => true

/-- The table with the facts of its text set from the definition that created it:
{name}`CatalogTable.inlineUnique` holds the columns with a UNIQUE constraint, and
{name}`CatalogTable.exactNames` says that the table-level keys, the foreign keys and the generated
expressions spell every column as it is declared. -/
def CatalogTable.withSpelling (definitions : List Syntax.ColumnDefinition)
    (constraints : List Syntax.TableConstraint) (table : CatalogTable) : CatalogTable :=
  { table with
    inlineUnique := (definitions.zipIdx.filter fun (definition, _) =>
      definition.constraints.any Syntax.ColumnConstraint.isUnique).map (·.2)
    exactNames := constraints.all (·.spelledAsDeclared table.columns) &&
      definitions.all fun definition => match definition.generatedExpression with
        | some (_, expression) => expression.spelledAsDeclared table.columns
        | none => true }

/-- Whether the key terms and the filter of an index are spelled as the columns of its table are
declared. -/
def indexSpelledAsDeclared (columns : List CatalogColumn) (terms : List Syntax.OrderTerm)
    (filter : Option Syntax.Expr) : Bool :=
  terms.all (·.expression.spelledAsDeclared columns) && (filter.map (·.spelledAsDeclared columns)).getD true

end Belay.Sqlite.Model
