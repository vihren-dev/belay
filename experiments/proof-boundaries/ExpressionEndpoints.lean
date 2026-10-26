import ExpressionAgreement
import Belay.Sqlite.Model.ExprAppendLaws
import Belay.Sqlite.Model.ExprContextLaws

set_option doc.verso true

/-! Experiment: three existing context/row laws use one evaluator induction. -/

namespace ProofBoundaries

open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- The constant-false test finds no expression node. Proof sketch: mutual induction
through the existing traversal; every disjunction has only false inputs. -/
theorem any_false (expression : Expr) : expression.any (fun _ => false) = false := by
  induction expression using Expr.rec
    (motive_2 := fun arguments => arguments.any (fun _ => false) = false) <;>
    simp_all [Expr.any, Arguments.any]

/-- Matching indexed subqueries at this row preserves value, fault and JSON subtype.
Unlike the existing endpoint, no fallible-call exclusion is needed: the shared proof
tracks argument subtypes as well as values. Proof sketch: every primitive read agrees. -/
theorem evaluate_withSubqueries (context : EvalContext) (row : List Value)
    (other : Nat → List Value → SubqueryRun) (agree : ∀ index, context.subqueries index row = other index row)
    (expression : Expr) :
    expression.evaluate { context with subqueries := other } row = expression.evaluate context row ∧
      expression.givesJson { context with subqueries := other } row = expression.givesJson context row := by
  apply evaluate_agrees _ _ row row (fun _ => false) _ expression (any_false expression)
  intro node _
  cases node <;> simp [NodeAgrees, ← agree]

/-- Appending unused cells retains the original endpoint's complete formula, including
JSON subtype and fault equality. Proof sketch: the column bound preserves each read;
row-independent subqueries preserve every subquery observation. -/
theorem evaluate_append (context : EvalContext) (rowFree : context.RowFree) {width : Nat}
    (row extra : List Value) (wide : width ≤ row.length) (expression : Expr)
    (below : expression.any (Expr.isColumnFrom width) = false) :
    expression.evaluate context (row ++ extra) = expression.evaluate context row ∧
      expression.givesJson context (row ++ extra) = expression.givesJson context row := by
  apply evaluate_agrees context context (row ++ extra) row (Expr.isColumnFrom width) _ expression below
  intro node allowed
  cases node
  case column position =>
    have inside : position < row.length := by
      simp only [Expr.isColumnFrom, ge_iff_le, decide_eq_false_iff_not, Nat.not_le] at allowed
      omega
    simp [NodeAgrees, List.getD_eq_getElem?_getD, List.getElem?_append_left inside]
  all_goals simp [NodeAgrees, fun index => rowFree index (row ++ extra) row]

/-- Marking first rows certain preserves expressions without scalar subqueries, even with
fallible calls. Existence and membership do not inspect that certainty field. Proof sketch:
each admitted node observes the same data, then apply the shared evaluator theorem. -/
theorem evaluate_certainFirst (context : EvalContext) (row : List Value) (expression : Expr)
    (noScalar : expression.any (· matches .subquery _) = false) :
    expression.evaluate { context with subqueries := fun index outer => (context.subqueries index outer).certainFirst } row =
      expression.evaluate context row ∧
    expression.givesJson { context with subqueries := fun index outer => (context.subqueries index outer).certainFirst } row =
      expression.givesJson context row := by
  apply evaluate_agrees _ _ row row (· matches .subquery _) _ expression noScalar
  intro node allowed
  cases node <;> simp_all [NodeAgrees, SubqueryRun.certainFirst]
  all_goals rfl

#print axioms evaluate_withSubqueries
#print axioms evaluate_append
#print axioms evaluate_certainFirst

end ProofBoundaries
