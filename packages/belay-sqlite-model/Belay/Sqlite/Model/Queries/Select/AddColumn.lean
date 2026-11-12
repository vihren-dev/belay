import Belay.Sqlite.Model.Queries.Preparation.Definitions

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Whether an expression is the keyword {lit}`NULL`. It lists every constructor, so a new
expression form needs a decision here. -/
def isNullKeyword : Syntax.Expr → Bool
  | .null => true
  | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .identifier .. | .qualified ..
  | .negate _ | .positive _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _
  | .call .. | .arithmetic .. | .cast .. | .collate .. | .exists _ | .inQuery .. | .subquery _
  | .inList .. | .between .. | .caseOf .. | .concatenate .. | .raise .. => false

end Belay.Sqlite.Model
