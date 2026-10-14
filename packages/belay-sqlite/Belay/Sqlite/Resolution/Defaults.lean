import Belay.Sqlite.Resolution.Values

set_option doc.verso true

/-! Literal defaults shared by INSERT and column extension. The catalog retains
written syntax; these functions evaluate it without adding resolved metadata. -/
namespace Belay.Sqlite

/-- The value of an admitted literal DEFAULT before column affinity applies.
NULL, numeric, text and blob literals are admitted, including a single sign on a
numeric literal. Bare identifiers are text, except unquoted TRUE and FALSE,
which are integers. Time keywords and compound expressions are model restrictions.
For example, {assert}`literalDefault (.string [49]) = .ok (.text [49])`. -/
def literalDefault : Syntax.Expr → Except ValueIssue Value
  | .null => .ok .null
  | .numeric text | .positive (.numeric text) => queryNumeric text false
  | .negate (.numeric text) => queryNumeric text true
  | .string bytes => .ok (.text bytes)
  | .blob bytes => .ok (.blob bytes)
  | .identifier name quoted =>
    if !quoted && normalizeIdentifier name == "true" then .ok (.integer 1)
    else if !quoted && normalizeIdentifier name == "false" then .ok (.integer 0)
    else .ok (.text name.toUTF8.toList)
  | .currentTime _ => .error (.restriction [] .timeValue)
  | .negate _ | .positive _ | .equals .. | .compare .. | .and .. | .or .. | .not _
  | .isNull .. | .callStar _ | .call .. | .arithmetic .. | .cast .. | .callPair .. =>
    .error (.restriction [] .unmodeledDefault)

/-- The value of a column's DEFAULT before affinity applies; NULL when it is
omitted. {name}`literalDefault` identifies unsupported expressions. INSERT's
full-row construction applies the column's affinity after evaluating this value.
Omit the default field for an ordinary nullable column. -/
def defaultValue (column : CatalogColumn) : Except ValueIssue Value :=
  match column.defaultValue with
  | none => .ok .null
  | some expression => literalDefault expression

end Belay.Sqlite
