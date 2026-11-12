import Belay.Sqlite.Model.Queries.Preparation.Values
import Belay.Sqlite.Model.Values.Scalar.Values

set_option doc.verso true

namespace Belay.Sqlite.Model

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
  | .currentTime _ | .parameter _ => .error (.restriction [] .unmodeledDefault)
  | .negate _ | .positive _ | .compare .. | .and .. | .or .. | .not _
  | .isNull .. | .callStar _ | .call .. | .arithmetic .. | .cast .. | .qualified .. | .collate .. | .exists _
  | .inQuery .. | .subquery _ | .inList .. | .between .. | .caseOf .. | .concatenate .. | .raise .. =>
    .error (.restriction [] .unmodeledDefault)

end Belay.Sqlite.Model
