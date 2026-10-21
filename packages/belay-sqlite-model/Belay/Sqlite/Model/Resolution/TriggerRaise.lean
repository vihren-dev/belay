import Belay.Sqlite.Model.Resolution.TriggerProgram
import Belay.Sqlite.Model.Resolution.Syntax

set_option doc.verso true

/-! The {lit}`RAISE` that a trigger's SELECT may have (ADR 0018, D5): the one result column of a
SELECT without {lit}`FROM` is {lit}`RAISE(...)`, or a {lit}`CASE` some of whose results are
{lit}`RAISE(...)`. Resolution resolves the column with each such result as NULL, and reads the
arms of the {lit}`CASE` from the arguments of its {lit}`iif` ({lit}`resolveCase`): a condition,
then the result of the condition, and the {lit}`ELSE` result last. A {lit}`RAISE` anywhere else
stays in the expression, and its resolution is the restriction of a {lit}`RAISE` form. -/

namespace Belay.Sqlite.Model

/-- The kind of a {lit}`RAISE` expression; none for another expression. -/
def Syntax.Expr.raiseKind? : Syntax.Expr → Option Syntax.RaiseKind
  | .raise kind _ => some kind
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .identifier .. | .qualified .. | .negate _
  | .positive _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic ..
  | .cast .. | .collate .. | .exists _ | .inQuery .. | .subquery _ | .inList .. | .between .. | .caseOf ..
  | .concatenate .. => none

/-- The message of a {lit}`RAISE` expression; none for {lit}`RAISE(IGNORE)` and for another
expression. -/
def Syntax.Expr.raiseMessage? : Syntax.Expr → Option Syntax.Expr
  | .raise _ message => message
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .identifier .. | .qualified .. | .negate _
  | .positive _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic ..
  | .cast .. | .collate .. | .exists _ | .inQuery .. | .subquery _ | .inList .. | .between .. | .caseOf ..
  | .concatenate .. => none

/-- The positions of the results among the operands of a {lit}`CASE` after its base: each odd
position, and the last one of an odd number of operands, the {lit}`ELSE` result. -/
def caseResult (count index : Nat) : Bool := index % 2 == 1 || (count % 2 == 1 && index + 1 == count)

/-- How the result column of a SELECT raises: the column with each {lit}`RAISE` result as NULL,
the kind of each operand of its {lit}`CASE` after the base (none for an operand that does not
raise), and the messages of the {lit}`RAISE` results; none for a column that does not raise
there. -/
def raisingColumn : Syntax.Expr → Option (Syntax.Expr × List (Option Syntax.RaiseKind) × List Syntax.Expr)
  | written@(.raise kind _) => some (.null, [some kind], written.raiseMessage?.toList)
  | .caseOf operands hasBase =>
    let base := if hasBase then operands.take 1 else []
    let rest := if hasBase then operands.drop 1 else operands
    let kinds := rest.zipIdx.map fun (operand, index) => if caseResult rest.length index then operand.raiseKind? else none
    if kinds.all (·.isNone) then none
    else some (.caseOf (base ++ rest.zipIdx.map fun (operand, index) =>
        if caseResult rest.length index && operand.raiseKind?.isSome then .null else operand) hasBase,
      kinds, rest.filterMap fun operand => if operand.raiseKind?.isSome then operand.raiseMessage? else none)
  | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .identifier .. | .qualified .. | .negate _
  | .positive _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic ..
  | .cast .. | .collate .. | .exists _ | .inQuery .. | .subquery _ | .inList .. | .between .. | .concatenate .. => none

/-- The arms of a raising {lit}`CASE` from the arguments of its {lit}`iif` and the kinds of the
operands: each condition with the kind of its result, and the kind of the {lit}`ELSE` result
last, none without {lit}`ELSE`. Lists of other lengths give no arm. -/
def raiseArms : List Resolved.Expr → List (Option Syntax.RaiseKind) →
    List (Resolved.Expr × Option Syntax.RaiseKind) × Option Syntax.RaiseKind
  | condition :: _ :: rest, _ :: kind :: kinds =>
    let (arms, otherwise) := raiseArms rest kinds
    ((condition, kind) :: arms, otherwise)
  | [_], [kind] => ([], kind)
  | [], _ | [_], [] | [_], _ :: _ :: _ | _ :: _ :: _, [] | _ :: _ :: _, [_] => ([], none)

end Belay.Sqlite.Model
