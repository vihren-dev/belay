import Belay.Sqlite.Model.Values.Scalar.Values

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The integer of a numeric value, if it is one. -/
def NumericValue.integer? : NumericValue → Option Int
  | .integer value => some value
  | .real | .hexTooBig => none

/-- The value of an integer literal, possibly negated; {lean}`(none : Option Int)`
for any other expression. -/
def integerLiteral : Syntax.Expr → Option Int
  | .numeric text => (numericValue text false).integer?
  | .negate operand => match operand with
    | .numeric text => (numericValue text true).integer?
    | .null | .string _ | .blob _ | .parameter _ | .currentTime _ | .identifier .. | .negate _ | .positive _
    | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic .. | .cast ..
    | .qualified .. | .collate .. | .exists _ | .inQuery .. | .subquery _ | .inList .. | .between .. | .caseOf ..
    | .concatenate .. | .raise .. => none
  | .null | .string _ | .blob _ | .parameter _ | .currentTime _ | .identifier .. | .positive _ | .compare ..
  | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic .. | .cast ..
  | .qualified .. | .collate .. | .exists _ | .inQuery .. | .subquery _ | .inList .. | .between .. | .caseOf ..
    | .concatenate .. | .raise .. => none

end Belay.Sqlite.Model
