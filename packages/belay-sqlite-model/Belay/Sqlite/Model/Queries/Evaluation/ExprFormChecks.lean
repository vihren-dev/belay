import Belay.Sqlite.Model.Queries.Evaluation.DerivedColumnTable
import Belay.Sqlite.Model.Queries.Evaluation.ExprCongruence
import Belay.Sqlite.Model.Queries.Evaluation.StatementCalm
import Belay.Sqlite.Model.Queries.Select.ExprAnyLaws

set_option doc.verso true

/-! Checks of the form of a resolved expression that give a property of its evaluation: a check that
the expression reads only its row gives {lit}`Resolved.Expr.ContextFree`, and a check that it has no
fallible call, clock read or counter call gives {lit}`Resolved.Expr.Calm`. A computation, such as the
kernel with {lit}`decide +kernel`, can evaluate the checks. -/

namespace Belay.Sqlite.Model.Resolved

/-- Whether a node of a resolved expression reads anything other than its row: the clock, a counter, an
aggregate value, a subquery or a parameter ({name}`Expr.readsBeyondRowAndParameters`, or a parameter).
Other nodes return false; {name}`Expr.any` checks their operands. For example, the column node of
{lit}`lower(email)` returns false, and the node of {lit}`?1` returns true. -/
def Expr.readsBeyondRow (node : Expr) : Bool :=
  node.readsBeyondRowAndParameters || node matches .parameter _

/-- For every resolved expression with no node that {name}`Expr.readsBeyondRow` finds, the expression is
context-free ({name}`Expr.ContextFree`): every two evaluation contexts give it the same value on every row.
Proof sketch: {name}`Expr.evaluate_congr` with the nodes of {name}`Expr.readsBeyondRow` masked; every node
that remains reads only the row. -/
theorem Expr.contextFree_of_rowOnly {expression : Expr} (rowOnly : expression.any Expr.readsBeyondRow = false) :
    expression.ContextFree := by
  intro first second cells
  refine congrArg Prod.fst (Expr.evaluate_congr first second cells cells Expr.readsBeyondRow ?_ expression
    rowOnly).1
  intro node allowed
  cases node <;> simp_all [Expr.readsBeyondRow, Expr.readsBeyondRowAndParameters, Expr.ReadsAgree]

/-- Whether a resolved expression is calm by its form: it has no fallible call, no read of the clock and
no call of a counter function ({name}`Expr.Calm` as a computation). -/
def Expr.calmCheck (expression : Expr) : Bool :=
  !expression.any Expr.isFallibleCall && !expression.any Expr.readsClockHere && !expression.any Expr.isCounter

/-- For every expression that passes {name}`Expr.calmCheck`, the expression is calm. Proof sketch: a node
that calls a counter function of some kind is a counter node ({name}`Expr.any_mono`). -/
theorem Expr.calm_of_calmCheck {expression : Expr} (checked : expression.calmCheck = true) : expression.Calm := by
  simp only [Expr.calmCheck, Bool.and_eq_true, Bool.not_eq_true'] at checked
  refine ⟨checked.1.1, checked.1.2, fun kind => ?_⟩
  cases found : expression.any (Expr.readsCounterHere kind)
  · rfl
  · have counter := Expr.any_mono _ Expr.isCounter (fun node hit => by
      cases node <;> simp_all [Expr.readsCounterHere, Expr.isCounter]) expression found
    rw [checked.2] at counter
    cases counter

end Belay.Sqlite.Model.Resolved
