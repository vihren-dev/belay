import Belay.Sqlite.Model.Resolution.Traced
import Belay.Sqlite.Model.Resolution.ExprForms

set_option doc.verso true

/-! The issues of expressions inside a traced computation: a child expression moves below the node
of its parent, and an operand is taken as a condition. -/

namespace Belay.Sqlite.Model

instance : Traced.Underable ValueIssue := ⟨ValueIssue.under⟩

/-- For every path and issue: moving an issue below a node is {name}`ValueIssue.under`. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem Traced.underable_valueIssue (path : List Nat) (issue : ValueIssue) :
    Traced.Underable.under path issue = issue.under path := rfl

/-- For every path: moving an issue below a node is {name}`ValueIssue.under`, as a function. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem Traced.underable_valueIssue_function (path : List Nat) :
    (Traced.Underable.under path : ValueIssue → ValueIssue) = ValueIssue.under path := rfl

/-- A condition inside a traced computation: the resolved expression of an operand, whose issue is
at {lit}`path`, as {name}`condition` takes it. The occurrences of the operand move below the node
of the condition. -/
def Traced.condition (path : List Nat) (operand : Traced ValueIssue Operand) : Traced ValueIssue Resolved.Expr :=
  (operand.under path).map (·.1)

/-- For every path and operand computation: the projection of {name}`Traced.condition` is
{name}`condition` of the projection. Proof sketch: unfold the definitions, push the projection through the monad with {lit}`traced_drop`, and split on the cases of the arm. -/
@[traced_drop] theorem Traced.drop_condition (path : List Nat) (operand : Traced ValueIssue Operand) :
    (Traced.condition path operand).drop = Belay.Sqlite.Model.condition path operand.drop := by
  unfold Traced.condition
  simp only [Traced.drop_map, Traced.drop_under]
  cases operand.drop <;> rfl

end Belay.Sqlite.Model
