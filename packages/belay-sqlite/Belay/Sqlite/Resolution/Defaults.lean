import Belay.Sqlite.Resolution.Values

set_option doc.verso true

/-! Literal defaults shared by INSERT and column extension. Resolution evaluates a written
default once ({lit}`resolveColumnDefault`) and stores the result in the catalog
({lit}`ColumnDefault`); {lit}`defaultValue` reads the stored INSERT value. -/
namespace Belay.Sqlite

/-- The value of an admitted literal DEFAULT before column affinity applies.
NULL, numeric, text and blob literals are admitted, including a single sign on a
numeric literal. Bare identifiers are text, except unquoted TRUE and FALSE,
which are integers. An oversized hexadecimal literal gives SQLite's
{name}`ExprError.hexLiteralTooBig` preparation error, a SQLite rule. Time keywords and compound expressions are model restrictions.
For example, {assert}`literalDefault (.string [49]) = .ok (.text [49])`. -/
def literalDefault : Syntax.Expr → Except ValueIssue Value
  | .null => .ok .null
  | .numeric text | .positive (.numeric text) => queryNumeric text false
  | .negate (.numeric text) => queryNumeric text true
  | .string bytes => .ok (.text bytes)
  | .blob bytes => .ok (.blob bytes)
  | .identifier name quote =>
    if quote == .none && name.isKeyword (bytes! "true") then .ok (.integer 1)
    else if quote == .none && name.isKeyword (bytes! "false") then .ok (.integer 0)
    else .ok (.text name.bytes)
  | .currentTime _ => .error (.restriction [] .unmodeledDefault)
  | .negate _ | .positive _ | .compare .. | .and .. | .or .. | .not _
  | .isNull .. | .callStar _ | .call .. | .arithmetic .. | .cast .. | .qualified .. =>
    .error (.restriction [] .unmodeledDefault)

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

end Belay.Sqlite
