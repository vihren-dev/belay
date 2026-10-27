import Belay.Sqlite.Model.InValueEqualsAny
import Belay.Sqlite.Model.Resolution.QueryAffinity

set_option doc.verso true

/-! The comparison of an integer probe (task 20261027, structural premises). When the probe of
{lit}`x IN (SELECT c FROM u)` is an integer and the comparison affinity is not TEXT, the {lit}`IN` test and the
correlated comparison {lit}`u.c = x` match the same candidates, whatever type, affinity and collation the
candidates have. The collation never matters, because an integer is less than every TEXT and no collation
changes an integer. The comparison affinity is not TEXT when one operand has INTEGER affinity, as a rowid alias
column has. The same holds for every comparison operator and for an integer on either side
({lit}`compareValue_integer_collation_free`). -/

namespace Belay.Sqlite.Model.Resolved

/-- For every collation, integer and value, the collation compares the integer with the value as BINARY does.
Proof sketch: no collation changes an integer or a value that is not TEXT; a TEXT is greater than the
integer under every collation, because the storage class decides before the bytes. -/
theorem compare_integer_collation_free (collation : Collation) (number : Int) (value : Value) :
    collation.compare (.integer number) value = Collation.binary.compare (.integer number) value := by
  have keyed : collation.key (.integer number) = .integer number := by cases collation <;> rfl
  cases value with
  | text bytes =>
    have above : ∀ other : List UInt8, Value.compare (.integer number) (.text other) = .lt := fun _ => by
      simp only [Value.compare, compareLex, compareOn, Value.rank, Ordering.then]
      rfl
    unfold Collation.compare
    rw [keyed]
    cases collation <;> simp only [Collation.key, above]
  | null | integer _ | real _ | blob _ => unfold Collation.compare; rw [keyed]; cases collation <;> rfl

/-- For every affinity other than TEXT, every integer and every value, {name}`comparisonOperands` keeps the
integer as its left operand. Proof sketch: NUMERIC, INTEGER and REAL affinity leave an integer as it is
({name}`numericOperand`), and BLOB or no affinity change nothing. -/
theorem comparisonOperands_integer_fst {affinity : Option Affinity} (notText : affinity ≠ some .text)
    (number : Int) (value : Value) : (comparisonOperands affinity (.integer number) value).1 = .integer number := by
  rcases affinity with _ | affinity
  · rfl
  · cases affinity <;> first | rfl | exact absurd rfl notText

/-- **Structural lemma.** For every affinity other than TEXT, every integer probe, every candidate and every two
collations, the {lit}`IN` test with the first collation matches the candidate exactly when the test with the
second collation matches it. So an {lit}`IN` test and a comparison {lit}`=` with the same affinity that have
different collations (for example NOCASE and BINARY), match the same candidates for an integer probe. A
candidate that is NULL matches in neither. Proof sketch: the left operand stays the integer
({name}`comparisonOperands_integer_fst`), and a collation compares an integer as BINARY does
({name}`compare_integer_collation_free`). -/
theorem inMatches_integer_collation_free {affinity : Option Affinity} (notText : affinity ≠ some .text)
    (first second : Collation) (number : Int) (candidate : Value) :
    inMatches affinity first (.integer number) candidate = inMatches affinity second (.integer number) candidate := by
  unfold inMatches
  rcases hp : comparisonOperands affinity (.integer number) candidate with ⟨a, b⟩
  have left := comparisonOperands_integer_fst notText number candidate
  rw [hp] at left
  simp only at left
  simp only [left, compare_integer_collation_free]

/-- For every affinity and two values, {name}`comparisonOperands` of the swapped values is the swapped result.
Proof sketch: each affinity applies the same change to both operands, and TEXT affinity decides by whether
either operand is TEXT, which does not depend on the order. -/
theorem comparisonOperands_swap (affinity : Option Affinity) (left right : Value) :
    comparisonOperands affinity right left =
      ((comparisonOperands affinity left right).2, (comparisonOperands affinity left right).1) := by
  rcases affinity with _ | affinity
  · rfl
  · cases affinity <;> simp [comparisonOperands, Bool.or_comm] <;> split <;> rfl

/-- For every affinity, collation and two values, the comparison {lit}`l = r` is the value of {lit}`r = l`. Proof
sketch: the operands swap ({name}`comparisonOperands_swap`), a NULL operand makes both NULL, and a collation
sees equal operands in either order. -/
theorem equalsValue_comm (affinity : Option Affinity) (collation : Collation) (left right : Value) :
    equalsValue affinity collation left right = equalsValue affinity collation right left := by
  unfold equalsValue compareValue
  rw [comparisonOperands_swap affinity left right]
  rcases comparisonOperands affinity left right with ⟨a, b⟩
  simp only
  unfold Comparison.apply
  have swap := Std.OrientedCmp.eq_swap (cmp := collation.compare) (a := a) (b := b)
  have same : (collation.compare b a == .eq) = (collation.compare a b == .eq) := by
    rw [swap]; cases collation.compare b a <;> rfl
  simp only [Comparison.holds, same, Bool.or_comm]

/-- For every collation, value and integer, the collation compares the value with the integer as BINARY does.
Proof sketch: the order is antisymmetric ({name}`Std.OrientedCmp.eq_swap`), so this is
{name}`compare_integer_collation_free` for the swapped operands. -/
theorem compare_collation_free_integer (collation : Collation) (value : Value) (number : Int) :
    collation.compare value (.integer number) = Collation.binary.compare value (.integer number) := by
  rw [Std.OrientedCmp.eq_swap (cmp := collation.compare), Std.OrientedCmp.eq_swap (cmp := Collation.binary.compare),
    compare_integer_collation_free]

/-- For every affinity other than TEXT, every value and every integer, {name}`comparisonOperands` keeps the
integer as its right operand. Proof sketch: {name}`comparisonOperands_swap` and
{name}`comparisonOperands_integer_fst`. -/
theorem comparisonOperands_integer_snd {affinity : Option Affinity} (notText : affinity ≠ some .text)
    (value : Value) (number : Int) : (comparisonOperands affinity value (.integer number)).2 = .integer number := by
  rw [comparisonOperands_swap affinity (.integer number) value]
  exact comparisonOperands_integer_fst notText number value

/-- For two collations {lit}`first` and {lit}`second` that order two given values the same way, every comparison
operator gives the same value for these values under {lit}`first` and under {lit}`second`. With {lit}`second` = BINARY
it says that a collation that compares the values as BINARY does gives the BINARY result. Proof sketch: {name}`Comparison.apply` uses the collation only through its
order of the two values. -/
theorem Comparison.apply_congr_compare (operator : Comparison) (left right : Value) {first second : Collation}
    (same : first.compare left right = second.compare left right) :
    operator.apply left right first = operator.apply left right second := by
  unfold Comparison.apply
  cases operator <;> simp [same]

/-- **Structural lemma for every comparison.** For every comparison operator ({lit}`=`, {lit}`<>`, {lit}`<`, {lit}`<=`,
{lit}`>`, {lit}`>=`), every affinity other than TEXT, every integer on the left, every value on the right, and every two
collations, {name}`compareValue` gives the same value under both collations. The same holds with the integer on the
right ({lit}`compareValue_collation_free_integer`). So a comparison with an integer operand does not depend on the
collation, whatever the other operand is. A NULL operand gives NULL for both. Proof sketch: the affinity keeps the integer
({name}`comparisonOperands_integer_fst`), and the collation compares an integer as BINARY does
({name}`compare_integer_collation_free`); the operator reads the collation only through that order
({name}`Comparison.apply_congr_compare`). -/
theorem compareValue_integer_collation_free (operator : Comparison) {affinity : Option Affinity}
    (notText : affinity ≠ some .text) (first second : Collation) (number : Int) (value : Value) :
    compareValue operator affinity first (.integer number) value =
      compareValue operator affinity second (.integer number) value := by
  unfold compareValue
  rcases hp : comparisonOperands affinity (.integer number) value with ⟨a, b⟩
  have left := comparisonOperands_integer_fst notText number value
  rw [hp] at left
  simp only at left
  subst left
  exact Comparison.apply_congr_compare _ _ _
    ((compare_integer_collation_free first number b).trans (compare_integer_collation_free second number b).symm)

/-- The same as {name}`compareValue_integer_collation_free` for an integer on the right. Proof sketch: as there, with
{name}`comparisonOperands_integer_snd` and {name}`compare_collation_free_integer`. -/
theorem compareValue_collation_free_integer (operator : Comparison) {affinity : Option Affinity}
    (notText : affinity ≠ some .text) (first second : Collation) (value : Value) (number : Int) :
    compareValue operator affinity first value (.integer number) =
      compareValue operator affinity second value (.integer number) := by
  unfold compareValue
  rcases hp : comparisonOperands affinity value (.integer number) with ⟨a, b⟩
  have right := comparisonOperands_integer_snd notText value number
  rw [hp] at right
  simp only at right
  subst right
  exact Comparison.apply_congr_compare _ _ _
    ((compare_collation_free_integer first a number).trans (compare_collation_free_integer second a number).symm)

end Belay.Sqlite.Model.Resolved

namespace Belay.Sqlite.Model

/-- For every two affinities, the comparison affinity ({name}`comparisonAffinity`) does not depend on the order
of the operands. Proof sketch: case analysis; two affinities give NUMERIC if either is numeric, which is
symmetric. -/
theorem comparisonAffinity_comm (left right : Option Affinity) :
    comparisonAffinity left right = comparisonAffinity right left := by
  rcases left with _ | left <;> rcases right with _ | right <;> simp [comparisonAffinity, Bool.or_comm]

/-- If one operand has INTEGER affinity, as a rowid alias column has, the comparison affinity is not TEXT, whatever
affinity the other operand has. Proof sketch: two affinities give NUMERIC, and a missing affinity gives INTEGER. -/
theorem comparisonAffinity_integer_ne_text (other : Option Affinity) :
    comparisonAffinity (some .integer) other ≠ some .text := by
  rcases other with _ | other <;> simp [comparisonAffinity]
  split <;> simp

end Belay.Sqlite.Model
