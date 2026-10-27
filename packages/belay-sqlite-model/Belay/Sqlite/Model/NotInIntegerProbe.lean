import Belay.Sqlite.Model.NotInValueLaw
import Belay.Sqlite.Model.Resolution.QueryAffinity

set_option doc.verso true

/-! The comparison of an integer probe (task 20261027, structural premises). When the probe of
{lit}`x IN (SELECT c FROM u)` is an integer and the comparison affinity is not TEXT, the {lit}`IN` test and the
correlated comparison {lit}`u.c = x` match the same candidates, whatever type, affinity and collation the
candidates have. The collation never matters, because an integer is less than every TEXT and no collation
changes an integer. The comparison affinity is not TEXT when one operand has INTEGER affinity, as a rowid alias
column has. -/

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
  unfold equalsValue
  rw [comparisonOperands_swap affinity left right]
  rcases comparisonOperands affinity left right with ⟨a, b⟩
  simp only
  unfold Comparison.apply
  have swap := Std.OrientedCmp.eq_swap (cmp := collation.compare) (a := a) (b := b)
  have same : (collation.compare b a == .eq) = (collation.compare a b == .eq) := by
    rw [swap]; cases collation.compare b a <;> rfl
  simp only [Comparison.holds, same, Bool.or_comm]

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
