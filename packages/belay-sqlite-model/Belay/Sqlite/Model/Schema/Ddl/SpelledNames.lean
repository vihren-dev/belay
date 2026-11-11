import Belay.Sqlite.Model.Schema.Columns.GeneratedColumns
import Belay.Sqlite.Model.Schema.Columns.Context
import Belay.Sqlite.Model.Queries.Preparation.SpelledNames

set_option doc.verso true

/-! How the text of a definition spells the columns that it names. SQLite keeps the text of a table and of
an index, and prints a name of it as written when the text no longer resolves, for example after a
column was dropped ({lit}`error in table t after drop column: no such column: b`). The model keeps no text
for generated columns, table-level keys, foreign keys and indexes, so it records whether the text spelled
every column name as the column is declared ({lit}`CatalogTable.exactNames`,
{lit}`CatalogIndex.exactNames`). A name with a double quote is not exact, because SQLite adds a hint about
string literals to its error for such a name. -/

namespace Belay.Sqlite.Model

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

end Belay.Sqlite.Model
