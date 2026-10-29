import Belay.Sqlite.Model.ExprEval
import Belay.Sqlite.Model.Resolution.ExprAny

set_option doc.verso true

/-! Expression congruence from the primitive observations of each node. -/

namespace Belay.Sqlite.Model.Resolved

/-- For two contexts and rows, the primitive reads of a node agree as follows.
Columns read equal cells; parameters read equal bound values; counters read equal optional
integers; aggregate slots read equal values. Clock keywords and date calls require equal clocks.
Existence reads equal emptiness flags and faults. Scalar subqueries read equal first cells
and equal faults after first-row certainty is considered. Membership reads equal first-column
lists and equal faults after row-set certainty is considered. Other nodes require nothing here;
{name}`Expr.any` checks their operands separately. For example, a literal needs no context
agreement. Use a constant-false mask with {name}`Expr.any` to allow every node. -/
def Expr.ReadsAgree (first second : EvalContext) (row other : List Value) : Expr → Prop
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
  | .literal _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic ..
  | .cast .. | .coalesce .. | .json .. | .scalar .. | .inList .. => True

/-- For any two contexts and rows, mask and expression: if {name}`Expr.ReadsAgree`
holds for every node the mask allows, and {name}`Expr.any` finds no forbidden node in the
expression, its value/fault pair and JSON subtype agree. A constant-false mask allows every
node; a column bound can allow only reads below a row width.
Proof sketch: use mutual induction over expressions and arguments. Combine equal operand
results; retain individual argument results for
lazy scalar calls and the argument values read by the JSON subtype calculation. -/
theorem Expr.evaluate_congr (first second : EvalContext) (row other : List Value)
    (forbidden : Expr → Bool) (agree : ∀ node, forbidden node = false → Expr.ReadsAgree first second row other node)
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
    simp only [Expr.ReadsAgree] at same
    exact ⟨congrArg (fun value => (value, Fault.none)) same, rfl⟩
  case now keyword =>
    have same := agree (.now keyword) allowed
    simp only [Expr.ReadsAgree] at same
    simp [Expr.evaluate, Expr.givesJson, same]
  case parameter number =>
    have same := agree (.parameter number) allowed
    simp only [Expr.ReadsAgree] at same
    simp [Expr.evaluate, Expr.givesJson, same]
  case counter kind =>
    have same := agree (.counter kind) allowed
    simp only [Expr.ReadsAgree] at same
    simp [Expr.evaluate, Expr.givesJson, same]
  case aggregateValue index =>
    have same := agree (.aggregateValue index) allowed
    simp only [Expr.ReadsAgree] at same
    exact ⟨congrArg (fun value => (value, Fault.none)) same, rfl⟩
  case «exists» index =>
    have same := agree (.exists index) allowed
    simp only [Expr.ReadsAgree] at same
    simp [Expr.evaluate, Expr.givesJson, same.1, same.2]
  case subquery index =>
    have same := agree (.subquery index) allowed
    simp only [Expr.ReadsAgree] at same
    simp [Expr.evaluate, Expr.givesJson, same.1, same.2]
  case inQuery operand index affinity collation negated ih =>
    obtain ⟨top, below⟩ := Bool.or_eq_false_iff.mp allowed
    have same := agree (.inQuery operand index affinity collation negated) top
    simp only [Expr.ReadsAgree] at same
    simp [Expr.evaluate, Expr.givesJson, (ih below).1, same.1, same.2]
  case date function arguments ih =>
    obtain ⟨top, below⟩ := Bool.or_eq_false_iff.mp allowed
    have same := agree (.date function arguments) top
    simp only [Expr.ReadsAgree] at same
    simp [Expr.evaluate, Expr.givesJson, (ih below).1, same]
  all_goals simp_all [Expr.any, Arguments.any, Expr.evaluate, Arguments.evaluate, Expr.givesJson,
      Arguments.givesJson]

/-- Whether a node reads a clock, counter, aggregate slot or subquery, rather than only
its row or parameters. Every date call counts as a clock read. Other nodes return false;
{name}`Expr.any` checks their operands. For example, an arithmetic node returns false even
when a nested operand reads the clock. Use {name}`Expr.any` for the whole expression. -/
def Expr.readsBeyondRowAndParameters : Expr → Bool
  | .now _ | .date .. | .counter _ | .aggregateValue _ | .exists _ | .subquery _ | .inQuery .. => true
  | .column _ | .literal _ | .parameter _ | .compare .. | .and .. | .or .. | .not _
  | .isNull .. | .arithmetic .. | .cast .. | .coalesce .. | .json .. | .scalar .. | .inList .. => false

/-- For every expression with no node accepted by {name}`Expr.readsBeyondRowAndParameters`,
two contexts with equal parameter lists give the same value/fault pair and JSON subtype over
any one row. This includes arithmetic, casts, scalar and JSON calls; it does not imply that
the expression has no fault.
Proof sketch: equal parameters and the same row give every admitted primitive read. -/
theorem Expr.evaluate_rowAndParameters (expression : Expr)
    (localReads : expression.any Expr.readsBeyondRowAndParameters = false)
    (first second : EvalContext) (row : List Value) (parameters : first.parameters = second.parameters) :
    expression.evaluate first row = expression.evaluate second row ∧
      expression.givesJson first row = expression.givesJson second row := by
  apply Expr.evaluate_congr first second row row Expr.readsBeyondRowAndParameters _ expression localReads
  intro node allowed
  cases node <;> simp_all [Expr.readsBeyondRowAndParameters, Expr.ReadsAgree]

end Belay.Sqlite.Model.Resolved
