import ExpressionEndpoints
import ExpressionRowwise

set_option doc.verso true

/-! Boundary checks: equal values alone lose JSON subtype and certainty changes can
change faults. These reductions use the kernel, not a native execution oracle. -/

namespace ProofBoundaries

open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- A fixed subquery with one integer row and uncertain first-row and row-set observations. -/
def uncertainContext : EvalContext :=
  { clock := 0, subqueries := fun _ _ =>
    { rows := [[.integer 7]], fault := .none, firstCertain := false, rowsCertain := false } }

/-- Marking the first row certain changes a scalar subquery's fault. This is why the
certainty corollary must still exclude scalar subqueries. Proof sketch: definitions reduce. -/
theorem scalar_certainty_matters :
    ((Expr.subquery 0).evaluate uncertainContext []).2 = .may ∧
      ((Expr.subquery 0).evaluate
        { uncertainContext with subqueries := fun index outer =>
          (uncertainContext.subqueries index outer).certainFirst } []).2 = .none := by
  constructor <;> rfl

/-- Membership reads row-set certainty separately from first-row certainty. Its uncertain
set keeps a possible fault even after first-row certainty changes. Proof sketch: reduction. -/
theorem membership_certainty_distinct :
    ((Expr.inQuery (.literal (.integer 7)) 0 none .binary false).evaluate
      { uncertainContext with subqueries := fun index outer =>
        (uncertainContext.subqueries index outer).certainFirst } []).2 = .may := rfl

/-- A JSON-producing call and ordinary text can have equal values and faults but different
subtypes. Therefore the shared induction must also preserve the JSON subtype. -/
theorem value_equality_does_not_preserve_subtype (context : EvalContext) :
    (Expr.json .array .nil).evaluate context [] = (Expr.literal (.text [91, 93])).evaluate context [] ∧
      (Expr.json .array .nil).givesJson context [] ≠ (Expr.literal (.text [91, 93])).givesJson context [] := by
  constructor
  · simp only [Expr.evaluate, Arguments.evaluate, Arguments.givesJson]
    decide
  · change true ≠ false
    decide

/-- A call excluded by the old no-fallible-call premise is covered by the new theorem.
The formula keeps the full value/fault pair, even when JSON decoding fails. -/
theorem fallible_json_context (context : EvalContext) (row : List Value)
    (other : Nat → List Value → SubqueryRun) (agree : ∀ index, context.subqueries index row = other index row) :
    let expression := Expr.json .json (.cons (.literal (.text [91])) .nil)
    expression.any Expr.isFallibleCall = true ∧
      expression.evaluate { context with subqueries := other } row = expression.evaluate context row :=
  ⟨rfl, (evaluate_withSubqueries context row other agree _).1⟩

/-- JSON calls fall outside the existing rowwise whitelist but need no extra context
when their arguments are literals. This is a strict extension of the reusable contract. -/
theorem json_local_beyond_rowwise :
    (Expr.json .array .nil).any readsBeyondRowAndParameters = false ∧
      ¬(Expr.json .array .nil).Rowwise := by
  constructor
  · rfl
  · intro rowwise
    cases rowwise

#print axioms scalar_certainty_matters
#print axioms membership_certainty_distinct
#print axioms value_equality_does_not_preserve_subtype
#print axioms fallible_json_context
#print axioms json_local_beyond_rowwise

end ProofBoundaries
