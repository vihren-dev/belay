import Belay.Sqlite.Model.ExprFault

set_option doc.verso true

/-! The truth of a value as a condition, and SQLite's {lit}`AND`, {lit}`OR` and {lit}`NOT` on
values. The evaluation of expressions ({lit}`ExprEval.lean`) computes the three operators with
{lit}`Value.and`, {lit}`Value.or` and {lit}`Value.not`, so the lemmas here are about the values
that it gives. -/

namespace Belay.Sqlite.Model

/-- SQL's three truth values. A {lit}`WHERE` keeps a row only for {lean}`Truth.true`. -/
inductive Truth where
  /-- True. -/
  | true
  /-- False. -/
  | false
  /-- Unknown: the condition is NULL. -/
  | unknown
  deriving Repr, DecidableEq

/-- The truth of a value as a condition: {lean}`Truth.unknown` for NULL, {lean}`Truth.true` for
a value that SQLite reads as true ({name}`Resolved.truthy`), and {lean}`Truth.false` for every
other value. For example, {assert}`(Value.integer 2).truth = .true`. -/
def Value.truth (value : Value) : Truth :=
  if value.isNull then .unknown else if Resolved.truthy value then .true else .false

/-- Three-valued AND: false when one side is false, else unknown when one side is unknown. -/
def Truth.and : Truth → Truth → Truth
  | .false, .false | .false, .true | .false, .unknown | .true, .false | .unknown, .false => .false
  | .unknown, .unknown | .unknown, .true | .true, .unknown => .unknown
  | .true, .true => .true

/-- Three-valued OR: true when one side is true, else unknown when one side is unknown. -/
def Truth.or : Truth → Truth → Truth
  | .true, .true | .true, .false | .true, .unknown | .false, .true | .unknown, .true => .true
  | .unknown, .unknown | .unknown, .false | .false, .unknown => .unknown
  | .false, .false => .false

/-- Three-valued NOT: unknown stays unknown. -/
def Truth.not : Truth → Truth
  | .true => .false
  | .false => .true
  | .unknown => .unknown

/-- SQLite's {lit}`a AND b`: 0 when one side is false, else NULL when one side is NULL, else 1. -/
def Value.and (a b : Value) : Value :=
  if Resolved.falsy a || Resolved.falsy b then Model.truth false else if a.isNull || b.isNull then .null else Model.truth true

/-- SQLite's {lit}`a OR b`: 1 when one side is true, else NULL when one side is NULL, else 0. -/
def Value.or (a b : Value) : Value :=
  if Resolved.truthy a || Resolved.truthy b then Model.truth true else if a.isNull || b.isNull then .null else Model.truth false

/-- SQLite's {lit}`NOT a`: NULL for NULL, else 1 when the value is not true, else 0. -/
def Value.not (value : Value) : Value :=
  if value.isNull then .null else Model.truth (!Resolved.truthy value)

/-- For every Boolean, SQLite reads the value 1 or 0 ({name}`truth`) as true exactly when the
Boolean is true. Proof sketch: each Boolean gives the integer 1 or 0, and the definitions
compute. -/
@[simp] theorem truthy_truth (holds : Bool) : Resolved.truthy (truth holds) = holds := by
  cases holds <;> rfl

/-- For every Boolean, the value 1 or 0 ({name}`truth`) is not NULL. Proof sketch: each Boolean
gives an integer, and the definitions compute. -/
@[simp] theorem isNull_truth (holds : Bool) : (truth holds).isNull = false := by
  cases holds <;> rfl

/-- NULL is NULL. Proof sketch: the definition computes. -/
@[simp] theorem Value.isNull_null : Value.null.isNull = true := rfl

/-- For every value: if it is NULL, SQLite does not read it as true. Proof sketch: case analysis
on the value; only NULL is NULL, and {name}`Resolved.truthy` gives false for it. -/
theorem Value.truthy_of_isNull {value : Value} (null : value.isNull = true) : Resolved.truthy value = false := by
  cases value <;> simp_all [Value.isNull, Resolved.truthy]

/-- For every value, its truth is {lean}`Truth.true` exactly when SQLite reads it as true
({name}`Resolved.truthy`), which is when a {lit}`WHERE` keeps its row. Proof sketch: split on whether the value is NULL
and, if not, on whether SQLite reads it as true; a NULL value is not true
({name}`Value.truthy_of_isNull`). -/
theorem Value.truth_eq_true (value : Value) : value.truth = .true ↔ Resolved.truthy value = true := by
  cases null : value.isNull
  · cases t : Resolved.truthy value <;> simp [Value.truth, null, t]
  · simp [Value.truth, null, Value.truthy_of_isNull null]

/-- For all values {lit}`a` and {lit}`b`, the truth of {lit}`a AND b` ({name}`Value.and`) is the
three-valued AND ({name}`Truth.and`) of their truths. Proof sketch: split on whether each value is
NULL and whether SQLite reads it as true; a NULL value is not true
({name}`Value.truthy_of_isNull`), and the values 1 and 0 are not NULL and are true and false
({name}`isNull_truth`, {name}`truthy_truth`), so each case simplifies to equal sides. -/
theorem Value.truth_and (a b : Value) : (a.and b).truth = a.truth.and b.truth := by
  cases na : a.isNull <;> cases nb : b.isNull <;>
    (try have := Value.truthy_of_isNull na) <;> (try have := Value.truthy_of_isNull nb) <;>
    cases ta : Resolved.truthy a <;> cases tb : Resolved.truthy b <;>
    simp_all [Value.and, Value.truth, Truth.and, Resolved.falsy]

/-- For all values {lit}`a` and {lit}`b`, the truth of {lit}`a OR b` ({name}`Value.or`) is the
three-valued OR ({name}`Truth.or`) of their truths. Proof sketch: the case split of
{name}`Value.truth_and`. -/
theorem Value.truth_or (a b : Value) : (a.or b).truth = a.truth.or b.truth := by
  cases na : a.isNull <;> cases nb : b.isNull <;>
    (try have := Value.truthy_of_isNull na) <;> (try have := Value.truthy_of_isNull nb) <;>
    cases ta : Resolved.truthy a <;> cases tb : Resolved.truthy b <;>
    simp_all [Value.or, Value.truth, Truth.or]

/-- For every value, the truth of {lit}`NOT a` ({name}`Value.not`) is the three-valued NOT
({name}`Truth.not`) of its truth. Proof sketch: split on whether the value is NULL and whether
SQLite reads it as true; each case simplifies to equal sides. -/
theorem Value.truth_not (value : Value) : value.not.truth = value.truth.not := by
  cases null : value.isNull
  · cases t : Resolved.truthy value <;> simp [Value.not, Value.truth, Truth.not, null, t]
  · simp [Value.not, Value.truth, Truth.not, null]

end Belay.Sqlite.Model
