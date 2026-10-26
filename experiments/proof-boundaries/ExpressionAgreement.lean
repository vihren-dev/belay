import Belay.Sqlite.Model.ExprEval
import Belay.Sqlite.Model.Resolution.ExprAny

set_option doc.verso true

/-! Experiment: share expression induction at the primitive observations of one node. -/

namespace ProofBoundaries

open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- Equal primitive observations for a single expression node. Recursive operands are
handled by the existing traversal. Subquery forms compare their own observations:
scalar first-row certainty, membership rows certainty, and existence each differ. -/
def NodeAgrees (first second : EvalContext) (row other : List Value) : Expr → Prop
  | .column position => row.getD position .null = other.getD position .null
  | .now _ | .date .. => first.clock = second.clock
  | .parameter number => parameterValue first.parameters number = parameterValue second.parameters number
  | .counter kind => first.counters.read kind = second.counters.read kind
  | .aggregateValue index => first.aggregates.getD index .null = second.aggregates.getD index .null
  | .exists index =>
    let a := first.subqueries index row
    let b := second.subqueries index other
    a.rows.isEmpty = b.rows.isEmpty ∧ a.fault = b.fault
  | .subquery index =>
    let a := first.subqueries index row
    let b := second.subqueries index other
    (a.rows.head?.bind List.head?).getD .null = (b.rows.head?.bind List.head?).getD .null ∧
      (if a.firstCertain then a.fault else .may) = (if b.firstCertain then b.fault else .may)
  | .inQuery _ index .. =>
    let a := first.subqueries index row
    let b := second.subqueries index other
    a.rows.filterMap List.head? = b.rows.filterMap List.head? ∧
      (if a.rowsCertain then a.fault else .may) = (if b.rowsCertain then b.fault else .may)
  | _ => True

/-- One mutual induction preserves value, fault and JSON subtype whenever the primitive
reads agree for all nodes outside a forbidden set, and the expression avoids that set.
Proof sketch: combine equal operand results; retain individual argument results for
lazy scalar calls and the argument values read by the JSON subtype calculation. -/
theorem evaluate_agrees (first second : EvalContext) (row other : List Value)
    (forbidden : Expr → Bool) (agree : ∀ node, forbidden node = false → NodeAgrees first second row other node)
    (expression : Expr) (allowed : expression.any forbidden = false) :
    expression.evaluate first row = expression.evaluate second other ∧
      expression.givesJson first row = expression.givesJson second other := by
  induction expression using Expr.rec
    (motive_2 := fun arguments => arguments.any forbidden = false →
      arguments.evaluate first row = arguments.evaluate second other ∧
        arguments.givesJson first row = arguments.givesJson second other ∧
        ∀ head tail, arguments = .cons head tail → head.evaluate first row = head.evaluate second other ∧
          tail.evaluate first row = tail.evaluate second other)
  case json function arguments ih =>
    have same := ih (by simpa [Expr.any] using (Bool.or_eq_false_iff.mp allowed).2)
    refine ⟨by simp only [Expr.evaluate, same.1, same.2], ?_⟩
    have values := congrArg Prod.fst same.1
    cases function <;> try rfl
    rcases arguments with _ | ⟨json, _ | ⟨path, _ | ⟨_, _⟩⟩⟩ <;> try rfl
    simp only [Arguments.evaluate, List.cons.injEq] at values
    simp only [Expr.givesJson, values.1, values.2.1]
  case scalar function arguments ih =>
    have same := ih (Bool.or_eq_false_iff.mp allowed).2
    cases function
    case iif =>
      rcases arguments with _ | ⟨condition, rest⟩
      · simp [Expr.evaluate, Expr.givesJson]
      · have parts := same.2.2 condition rest rfl
        simp [Expr.evaluate, Expr.givesJson, parts.1, parts.2]
    all_goals simp [Expr.evaluate, Expr.givesJson, same.1]
  case column position =>
    have same := agree (.column position) allowed
    simp only [NodeAgrees] at same
    exact ⟨congrArg (fun value => (value, Fault.none)) same, rfl⟩
  case now keyword =>
    have same := agree (.now keyword) allowed
    simp only [NodeAgrees] at same
    simp [Expr.evaluate, Expr.givesJson, same]
  case parameter number =>
    have same := agree (.parameter number) allowed
    simp only [NodeAgrees] at same
    simp [Expr.evaluate, Expr.givesJson, same]
  case counter kind =>
    have same := agree (.counter kind) allowed
    simp only [NodeAgrees] at same
    simp [Expr.evaluate, Expr.givesJson, same]
  case aggregateValue index =>
    have same := agree (.aggregateValue index) allowed
    simp only [NodeAgrees] at same
    exact ⟨congrArg (fun value => (value, Fault.none)) same, rfl⟩
  case «exists» index =>
    have same := agree (.exists index) allowed
    simp only [NodeAgrees] at same
    simp [Expr.evaluate, Expr.givesJson, same.1, same.2]
  case subquery index =>
    have same := agree (.subquery index) allowed
    simp only [NodeAgrees] at same
    simp [Expr.evaluate, Expr.givesJson, same.1, same.2]
  case inQuery operand index affinity collation negated ih =>
    obtain ⟨top, below⟩ := Bool.or_eq_false_iff.mp allowed
    have same := agree (.inQuery operand index affinity collation negated) top
    simp only [NodeAgrees] at same
    simp [Expr.evaluate, Expr.givesJson, (ih below).1, same.1, same.2]
  case date function arguments ih =>
    obtain ⟨top, below⟩ := Bool.or_eq_false_iff.mp allowed
    have same := agree (.date function arguments) top
    simp only [NodeAgrees] at same
    simp [Expr.evaluate, Expr.givesJson, (ih below).1, same]
  all_goals simp_all [Expr.any, Arguments.any, Expr.evaluate, Arguments.evaluate, Expr.givesJson,
      Arguments.givesJson]

#print axioms evaluate_agrees

end ProofBoundaries
