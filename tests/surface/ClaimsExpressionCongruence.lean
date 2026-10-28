import Belay.Sqlite.Model.ExprContextLaws
import Belay.Sqlite.Model.RowwiseExpr

set_option doc.verso true

/-! Current congruence contracts and the observations they must keep separate. -/

open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- Arbitrary subquery replacement needs no fallible-call exclusion and preserves subtype. -/
example (context : EvalContext) (row : List Value) (other : Nat → List Value → SubqueryRun)
    (agree : ∀ index, context.subqueries index row = other index row) (expression : Expr) :
    expression.evaluate { context with subqueries := other } row = expression.evaluate context row ∧
      expression.givesJson { context with subqueries := other } row = expression.givesJson context row :=
  expression.evaluate_withSubqueries context row other agree

/-- Certainty replacement excludes scalar subqueries, but permits fallible calls. -/
example (context : EvalContext) (row : List Value) (expression : Expr)
    (noScalar : expression.any (· matches .subquery _) = false) :
    expression.evaluate { context with subqueries := fun index outer =>
      (context.subqueries index outer).certainFirst } row = expression.evaluate context row ∧
    expression.givesJson { context with subqueries := fun index outer =>
      (context.subqueries index outer).certainFirst } row = expression.givesJson context row :=
  expression.evaluate_certainFirst context row noScalar

/-- A run whose first row and complete row set are both uncertain. -/
def uncertainContext : EvalContext :=
  { clock := 0, subqueries := fun _ _ =>
    { rows := [[.integer 7]], fault := .none, firstCertain := false, rowsCertain := false } }

/-- Scalar subqueries observe first certainty; membership retains independent row uncertainty. -/
example :
    ((Expr.subquery 0).evaluate uncertainContext []).2 = .may ∧
    ((Expr.subquery 0).evaluate { uncertainContext with subqueries := fun index outer =>
      (uncertainContext.subqueries index outer).certainFirst } []).2 = .none ∧
    ((Expr.inQuery (.literal (.integer 7)) 0 none .binary false).evaluate
      { uncertainContext with subqueries := fun index outer =>
        (uncertainContext.subqueries index outer).certainFirst } []).2 = .may := ⟨rfl, rfl, rfl⟩

/-- A literal-only JSON call is local, outside Rowwise, and can certainly fail. -/
def malformedJson : Expr := .json .json (.cons (.literal (.text [91])) .nil)

/-- Locality permits fallible JSON, whereas Rowwise supplies a separate fault-free contract. -/
example (context : EvalContext) (row : List Value) :
    malformedJson.any Expr.readsBeyondRowAndParameters = false ∧
      ¬malformedJson.Rowwise ∧ (malformedJson.evaluate context row).2 = .must := by
  refine ⟨rfl, (fun certificate => by cases certificate), ?_⟩
  simp only [malformedJson, Expr.evaluate, Arguments.evaluate, Arguments.givesJson, Expr.givesJson]
  decide +kernel

/-- The stronger context law applies to the malformed call excluded by the old premise. -/
example (context : EvalContext) (row : List Value) (other : Nat → List Value → SubqueryRun)
    (agree : ∀ index, context.subqueries index row = other index row) :
    malformedJson.any Expr.isFallibleCall = true ∧
    malformedJson.evaluate { context with subqueries := other } row = malformedJson.evaluate context row ∧
    malformedJson.givesJson { context with subqueries := other } row = malformedJson.givesJson context row :=
  ⟨rfl, malformedJson.evaluate_withSubqueries context row other agree⟩

/-- Equal values and faults alone do not preserve JSON subtype. -/
example (context : EvalContext) :
    (Expr.json .array .nil).evaluate context [] = (Expr.literal (.text [91, 93])).evaluate context [] ∧
    (Expr.json .array .nil).givesJson context [] ≠ (Expr.literal (.text [91, 93])).givesJson context [] := by
  constructor
  · simp only [Expr.evaluate, Arguments.evaluate, Arguments.givesJson]
    decide
  · change true ≠ false
    decide

/-- A fixed subquery whose NULL result comes with a certain fault. -/
def failingContext : EvalContext :=
  { clock := 0, subqueries := fun _ _ => { rows := [], fault := .must } }

/-- A fault in the first lazy operand remains certain. -/
def firstFault : Arguments := .cons (.subquery 0) (.cons (.literal .null) .nil)

/-- The same fault in a later lazy operand can be skipped. -/
def laterFault : Arguments := .cons (.literal .null) (.cons (.subquery 0) .nil)

/-- Whole argument results agree, but IIF needs individual operand faults to distinguish
its mandatory head from its optional tail. The shared induction retains those results. -/
example : firstFault.evaluate failingContext [] = laterFault.evaluate failingContext [] ∧
    ((Expr.scalar .iif firstFault).evaluate failingContext []).2 = .must ∧
    ((Expr.scalar .iif laterFault).evaluate failingContext []).2 = .may := ⟨rfl, rfl, rfl⟩

/-- Locality keeps faults as well as values when unrelated context fields change. -/
example (first second : EvalContext) (row : List Value) (parameters : first.parameters = second.parameters) :
    malformedJson.evaluate first row = malformedJson.evaluate second row ∧
      malformedJson.givesJson first row = malformedJson.givesJson second row :=
  malformedJson.evaluate_rowAndParameters rfl first second row parameters

#print axioms Expr.evaluate_congr
#print axioms Expr.Rowwise.localReads
#print axioms Expr.any_false
