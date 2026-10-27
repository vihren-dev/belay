import Belay.Sqlite.Model.InValueLaws
import Belay.Sqlite.Model.StoreValueLaws

set_option doc.verso true

/-! {lit}`x NOT IN (SELECT c FROM u)` against {lit}`NOT (x = c1 OR x = c2 OR ...)` (task
20261027, value law). {name}`Belay.Sqlite.Model.Resolved.inValue` takes the affinity and the collation of the
{lit}`IN` test, and a comparison {lit}`x = c` takes its own affinity and collation, so the two are separate
parameters here. This module has no fact about a table, a schema or a catalog. -/

namespace Belay.Sqlite.Model.Resolved

/-- Whether a candidate matches the probe in an {lit}`IN` test: the candidate is not NULL and compares equal
to the probe after the affinity is applied ({name}`comparisonOperands`) under the collation. This is the
test that {name}`inValue` makes for each candidate. -/
def inMatches (affinity : Option Affinity) (collation : Collation) (value candidate : Value) : Bool :=
  let (a, b) := comparisonOperands affinity value candidate
  !b.isNull && collation.compare a b == .eq

/-- The value of the comparison {lit}`left op right` for any comparison operator with an affinity and a collation, as
{name}`Expr.evaluate` computes it for {lit}`Expr.compare`: the operands go through {name}`comparisonOperands`, and then
{name}`Comparison.apply` compares them. -/
def compareValue (operator : Comparison) (affinity : Option Affinity) (collation : Collation)
    (left right : Value) : Value :=
  let (a, b) := comparisonOperands affinity left right
  operator.apply a b collation

/-- The value of the comparison {lit}`left = right`: {name}`compareValue` for the operator {lit}`=`. -/
def equalsValue (affinity : Option Affinity) (collation : Collation) (left right : Value) : Value :=
  compareValue .eq affinity collation left right

/-- The value of {lit}`x = c1 OR x = c2 OR ...` over the candidates, with the affinity and the collation of
the comparison {lit}`=`. The disjunction of no comparison is 0. -/
def equalsAny (affinity : Option Affinity) (collation : Collation) (value : Value) (candidates : List Value) : Value :=
  candidates.foldr (fun candidate rest => (equalsValue affinity collation value candidate).or rest) (truth false)

/-- For all bits, {name}`integerAffinity` gives a number, not NULL. Proof sketch: it gives an integer
or a REAL. -/
theorem integerAffinity_isNull (bits : UInt64) : (integerAffinity bits).isNull = false := by
  unfold integerAffinity; split <;> rfl

/-- For all text bytes, the number-or-text of {name}`numericText` is not NULL. Proof sketch: the
text stays text, or {name}`textNumber` gives an integer or the result of {name}`integerAffinity`. -/
theorem numericText_isNull (bytes : List UInt8) : (numericText bytes).isNull = false := by
  unfold numericText textNumber
  rcases atof bytes with ⟨double, code⟩
  dsimp only
  split
  · rfl
  · split
    · rfl
    · exact integerAffinity_isNull _

/-- For every value, {name}`numericOperand` gives NULL exactly for NULL. Proof sketch: only a text changes,
and {name}`numericText_isNull` covers it. -/
theorem numericOperand_isNull (value : Value) : (numericOperand value).isNull = value.isNull := by
  cases value
  case text bytes => exact numericText_isNull bytes
  all_goals rfl

/-- For every value, {name}`numericStore` gives NULL exactly for NULL. Proof sketch: a REAL becomes
the result of {name}`integerAffinity`, a text the result of {name}`numericText`, and the others stay. -/
theorem numericStore_isNull (value : Value) : (numericStore value).isNull = value.isNull := by
  cases value
  case real bits => exact integerAffinity_isNull bits
  case text bytes => exact numericText_isNull bytes
  all_goals rfl

/-- For every value, {name}`realRead` gives NULL exactly for NULL. Proof sketch: a number becomes a
REAL, and the others stay. -/
theorem realRead_isNull (value : Value) : (realRead value).isNull = value.isNull := by
  cases value <;> rfl

/-- For every affinity and value, {name}`Value.store` with the affinity gives NULL exactly for NULL. Proof
sketch: case analysis on the affinity and the value; a stored number or text is never NULL. -/
theorem store_isNull (affinity : Affinity) (value : Value) : (Value.store affinity value).isNull = value.isNull := by
  cases affinity <;> cases value <;> simp only [Value.store] <;>
    first
    | rfl
    | exact numericStore_isNull _
    | (rw [realRead_isNull]; exact numericStore_isNull _)

/-- For every affinity and operands, {name}`comparisonOperands` keeps the NULL state of both operands: the
left result is NULL exactly when the left operand is, and the same for the right. Proof sketch: each
branch of the definition applies {name}`numericOperand` or {name}`Value.store`, which keep NULL
({name}`numericOperand_isNull`, {name}`store_isNull`). -/
theorem comparisonOperands_isNull (affinity : Option Affinity) (left right : Value) :
    (comparisonOperands affinity left right).1.isNull = left.isNull ∧
      (comparisonOperands affinity left right).2.isNull = right.isNull := by
  rcases affinity with _ | affinity
  · exact ⟨rfl, rfl⟩
  · cases affinity <;> simp only [comparisonOperands, numericOperand_isNull, and_self] <;> try exact ⟨rfl, rfl⟩
    all_goals split <;> simp only [store_isNull, and_self]

/-- For every affinity, collation, probe and candidates, {name}`inValue` is its four cases: the value of an empty
list (1 when negated), NULL for a NULL probe, the value of a match, and NULL for a NULL candidate, else the
value of no match. Proof sketch: the right side is the definition of {name}`inValue`, with the test of a
candidate named {name}`inMatches`. -/
theorem inValue_cases (affinity : Option Affinity) (collation : Collation) (negated : Bool) (value : Value)
    (candidates : List Value) :
    inValue affinity collation negated value candidates =
      if candidates.isEmpty then truth negated
      else if value.isNull then .null
      else if candidates.any (inMatches affinity collation value) then truth (!negated)
      else if candidates.any (·.isNull) then .null
      else truth negated := rfl

/-- For two tests that agree on every element of a list, the list has an element that passes the first
exactly when it has one that passes the second. Proof sketch: induction on the list. -/
theorem any_congr_of_mem {α : Type} {elements : List α} {first second : α → Bool}
    (agree : ∀ element ∈ elements, first element = second element) : elements.any first = elements.any second := by
  induction elements with
  | nil => rfl
  | cons element rest ih =>
    simp only [List.any_cons, agree element (by simp),
      ih (fun other member => agree other (by simp [member]))]

end Belay.Sqlite.Model.Resolved
