import Belay.Sqlite.Model.Queries.Preparation.Values
import Belay.Sqlite.Model.Values.Scalar.Values

set_option doc.verso true

/-! Literal defaults shared by INSERT and column extension. Resolution evaluates a written
default once ({lit}`resolveColumnDefault`) and stores the result in the catalog
({lit}`ColumnDefault`); {lit}`defaultValue` reads the stored INSERT value. -/
namespace Belay.Sqlite.Model

/-- The value that an INSERT gives an omitted column, before affinity applies: NULL without a
default, the stored INSERT value of a literal default, SQLite's {lit}`hex literal too big`
for an oversized hexadecimal default, and a model restriction for a time keyword default,
whose value the execution gives instead ({lit}`omittedCell`). INSERT's full-row
construction applies the column's affinity after this value. -/
def defaultValue (column : CatalogColumn) : Except ValueIssue Value :=
  match column.defaultValue with
  | none => .ok .null
  | some { form := .literal (.value value) _, .. } => .ok value
  | some { form := .literal (.hexLiteralTooBig text) _, .. } => .error (.prepare (.hexLiteralTooBig text))
  | some { form := .clock _, .. } => .error (.restriction [] .unmodeledDefault)

end Belay.Sqlite.Model
