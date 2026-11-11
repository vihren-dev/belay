import Belay.Sqlite.Model.Shared.Resolved.TriggerProgram

set_option doc.verso true

/-! The {lit}`RAISE` that a trigger's SELECT may have (ADR 0018, D5): the one result column of a
SELECT without {lit}`FROM` is {lit}`RAISE(...)`, or a {lit}`CASE` some of whose results are
{lit}`RAISE(...)`. Resolution resolves the column with each such result as NULL, and reads the
arms of the {lit}`CASE` from the arguments of its {lit}`iif` ({lit}`resolveCase`): a condition,
then the result of the condition, and the {lit}`ELSE` result last. A {lit}`RAISE` anywhere else
stays in the expression, and its resolution is the restriction of a {lit}`RAISE` form. -/

namespace Belay.Sqlite.Model

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
