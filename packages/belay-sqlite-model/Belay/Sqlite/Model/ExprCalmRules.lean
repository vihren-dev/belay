import Belay.Sqlite.Model.ExprCalmLaws

set_option doc.verso true

/-! The calm rules of the resolved expressions that {lit}`ExprCalmLaws.lean` does not cover
(ADR 0027 D1, expression phase). An expression is calm ({name}`Belay.Sqlite.Model.Resolved.Expr.Calm`)
when no part of it is a fallible call, a clock read or a counter call; the execution rule reads
a calm statement with a context of its values alone. Arithmetic, {lit}`CAST`, {lit}`COALESCE` and
{lit}`IN` of a list are calm when their parts are; a call of a function that cannot fail is calm
when its arguments are ({lit}`Arguments.Calm`); a time keyword, a
counter call and a JSON call are never calm. -/

namespace Belay.Sqlite.Model.Resolved

/-- Calm arguments of a call: no argument has a fallible call, a clock read or a counter call
in any of its parts, as {name}`Expr.Calm` says of an expression. -/
def Arguments.Calm (arguments : Arguments) : Prop :=
  arguments.any Expr.isFallibleCall = false ∧ arguments.any Expr.readsClockHere = false ∧
    ∀ kind, arguments.any (Expr.readsCounterHere kind) = false

/-- No arguments are calm. Proof sketch: the tests find nothing in no arguments. -/
theorem Arguments.calm_nil : Arguments.nil.Calm := by simp [Arguments.Calm, Arguments.any]

/-- Arguments are calm exactly when the first is calm and the others are. Proof sketch: the
tests on the arguments are the tests on the first or on the others. -/
theorem Arguments.calm_cons (head : Expr) (tail : Arguments) :
    (Arguments.cons head tail).Calm ↔ head.Calm ∧ tail.Calm := by
  simp only [Arguments.Calm, Expr.Calm, Arguments.any, Bool.or_eq_false_iff]
  grind

/-- Arithmetic is calm exactly when both operands are calm. Proof sketch: the operator is no
fallible call, clock read or counter call itself. -/
theorem Expr.calm_arithmetic (operator : ArithmeticOperator) (left right : Expr) :
    (Expr.arithmetic operator left right).Calm ↔ left.Calm ∧ right.Calm := by
  simp only [Expr.Calm, Expr.any, Expr.isFallibleCall, Expr.readsClockHere, Expr.readsCounterHere,
    Bool.false_or, Bool.or_eq_false_iff]
  grind

/-- {lit}`CAST` is calm exactly when its operand is calm. Proof sketch: as
{name}`Expr.calm_arithmetic`. -/
theorem Expr.calm_cast (affinity : Affinity) (operand : Expr) : (Expr.cast affinity operand).Calm ↔ operand.Calm := by
  simp only [Expr.Calm, Expr.any, Expr.isFallibleCall, Expr.readsClockHere, Expr.readsCounterHere, Bool.false_or]

/-- {lit}`COALESCE` is calm exactly when both operands are calm. Proof sketch: as
{name}`Expr.calm_arithmetic`. -/
theorem Expr.calm_coalesce (first rest : Expr) : (Expr.coalesce first rest).Calm ↔ first.Calm ∧ rest.Calm := by
  simp only [Expr.Calm, Expr.any, Expr.isFallibleCall, Expr.readsClockHere, Expr.readsCounterHere,
    Bool.false_or, Bool.or_eq_false_iff]
  grind

/-- An aggregate value is calm. Proof sketch: it is no fallible call, clock read or counter call. -/
theorem Expr.calm_aggregateValue (index : Nat) : (Expr.aggregateValue index).Calm := by
  simp [Expr.Calm, Expr.any, Expr.isFallibleCall, Expr.readsClockHere, Expr.readsCounterHere]

/-- {lit}`x [NOT] IN (values)` is calm exactly when the operand and the values are calm. Proof
sketch: as {name}`Expr.calm_arithmetic`. -/
theorem Expr.calm_inList (operand : Expr) (values : Arguments) (affinity : Option Affinity) (collation : Collation)
    (negated : Bool) :
    (Expr.inList operand values affinity collation negated).Calm ↔ operand.Calm ∧ values.Calm := by
  simp only [Expr.Calm, Arguments.Calm, Expr.any, Expr.isFallibleCall, Expr.readsClockHere, Expr.readsCounterHere,
    Bool.false_or, Bool.or_eq_false_iff]
  grind

/-- A call of a scalar function is calm exactly when the function cannot fail
({name}`ScalarFunction.canFail`) and its arguments are calm. {lit}`iif`, and so {lit}`CASE`, cannot
fail. Proof sketch: the call is a fallible call exactly when the function can fail, and it is no
clock read or counter call. -/
theorem Expr.calm_scalar (function : ScalarFunction) (arguments : Arguments) :
    (Expr.scalar function arguments).Calm ↔ function.canFail = false ∧ arguments.Calm := by
  simp only [Expr.Calm, Arguments.Calm, Expr.any, Expr.isFallibleCall, Expr.readsClockHere, Expr.readsCounterHere,
    Bool.false_or, Bool.or_eq_false_iff]
  grind

/-- A call of a date and time function is calm exactly when it does not read {lit}`now`
({name}`DateFunction.readsNow`) and its arguments are calm. Proof sketch: as
{name}`Expr.calm_scalar`, with the clock read of the call. -/
theorem Expr.calm_date (function : DateFunction) (arguments : Arguments) :
    (Expr.date function arguments).Calm ↔ function.readsNow arguments = false ∧ arguments.Calm := by
  simp only [Expr.Calm, Arguments.Calm, Expr.any, Expr.isFallibleCall, Expr.readsClockHere, Expr.readsCounterHere,
    Bool.false_or, Bool.or_eq_false_iff]
  grind

/-- A time keyword is not calm: it reads the clock. Proof sketch: the keyword is a clock read
({lit}`Expr.readsClockHere`). -/
theorem Expr.not_calm_now (keyword : TimeKeyword) : ¬ (Expr.now keyword).Calm := by
  simp [Expr.Calm, Expr.any, Expr.readsClockHere]

/-- A counter call is not calm: it reads the counter of its kind. Proof sketch: the call is a counter
read ({lit}`Expr.readsCounterHere`). -/
theorem Expr.not_calm_counter (kind : CounterKind) : ¬ (Expr.counter kind).Calm := by
  simp [Expr.Calm, Expr.any, Expr.readsCounterHere]

/-- A JSON call is not calm: it is a fallible call. Proof sketch: every JSON call is a fallible call
({lit}`Expr.isFallibleCall`). -/
theorem Expr.not_calm_json (function : JsonFunction) (arguments : Arguments) : ¬ (Expr.json function arguments).Calm := by
  simp [Expr.Calm, Expr.any, Expr.isFallibleCall]

end Belay.Sqlite.Model.Resolved
