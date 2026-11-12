import Belay.Sqlite.Model.Queries.Select.OperandArms

set_option doc.verso true

/-! The remaining equations of {lit}`resolveOperand`, and those of {lit}`resolveArguments` and
{lit}`resolveCase`: calls, constants, subqueries and the forms built from several operands. They
have the shape that the functions had before the name trace was threaded through them. -/

namespace Belay.Sqlite.Model

variable (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (misuse : Bool)

/-- For every time keyword: the clock value of the statement. Proof sketch: both sides are equal by definition. -/
@[traced_arms] theorem resolveOperand_arm_currentTime (keyword : String) :
    resolveOperand dqs scope shapes misuse (.currentTime keyword) = .ok (.now (timeKeywordNamed keyword), none) := rfl

end Belay.Sqlite.Model
