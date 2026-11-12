import Belay.Sqlite.Model.Frontend.Grammar.Operators
import Belay.Sqlite.Model.Shared.Execution.Comparison

set_option doc.verso true

/-! The Values level of ADR 0012: SQLite's comparison of two stored values, as
"Comparison Expressions" and "Sort Order" of the pinned {lit}`datatype3.html`
state it. Each value maps to a sort key of three parts, compared in order: the
storage class, the exact number, and the bytes. -/

namespace Belay.Sqlite.Model

/-- For all values, {name}`Value.compare` is a transitive, oriented comparison: a total
preorder, as a sort and a grouping need. The proof is the core instance for a
lexicographic combination of keyed comparisons. -/
instance : Std.TransCmp Value.compare := by
  unfold Value.compare; exact inferInstance


/-- For every value of nonzero rank ({name}`Value.rank`), NULL comes before it in
{name}`Value.compare`. Rank 0 holds NULL and also a NaN REAL, which the model never makes and
which compares equal to NULL. Proof sketch: NULL has rank 0, and a nonzero rank is positive, so
the first comparison of {name}`Value.compare`, by rank, gives {lean}`Ordering.lt`. -/
theorem Value.compare_null (value : Value) (ranked : value.rank ≠ 0) : Value.compare .null value = .lt := by
  have before : Ord.compare (0 : Nat) value.rank = .lt := Nat.compare_eq_lt.mpr (Nat.pos_of_ne_zero ranked)
  have null : Value.rank .null = 0 := rfl
  simp only [Value.compare, compareLex, compareOn, null, before, Ordering.then]

/-- The name of a collation in capitals, as SQLite registers it: {lit}`BINARY`, {lit}`NOCASE` or
{lit}`RTRIM`. {name}`Collation.named?` reads each name back. -/
def Collation.sqlName : Collation → String
  | .binary => "BINARY"
  | .nocase => "NOCASE"
  | .rtrim => "RTRIM"

/-- The bytes without trailing spaces (0x20), as {lit}`rtrimCollFunc` removes them. -/
def trimTrailingSpaces (bytes : List UInt8) : List UInt8 := (bytes.reverse.dropWhile (· == 32)).reverse

/-- The value that a collation compares in place of a value: TEXT with folded ASCII
capitals ({lit}`NOCASE`) or without trailing spaces ({lit}`RTRIM`); every other value, and
every value under {lit}`BINARY`, as it is. -/
def Collation.key : Collation → Value → Value
  | .binary, value => value
  | .nocase, .text bytes => .text (bytes.map lowerAscii)
  | .rtrim, .text bytes => .text (trimTrailingSpaces bytes)
  | .nocase, value@.null | .nocase, value@(.integer _) | .nocase, value@(.real _) | .nocase, value@(.blob _)
  | .rtrim, value@.null | .rtrim, value@(.integer _) | .rtrim, value@(.real _) | .rtrim, value@(.blob _) => value

/-- SQLite's comparison of two values under a collation: {name}`Value.compare` of their
collation keys ({name}`Collation.key`). Under {lit}`BINARY` it is {name}`Value.compare`. -/
def Collation.compare (collation : Collation) (left right : Value) : Ordering :=
  Value.compare (collation.key left) (collation.key right)

/-- For every collation, {name}`Collation.compare` is a transitive, oriented comparison, as
a sort and a grouping need: it is {name}`Value.compare` of the keys. -/
instance (collation : Collation) : Std.TransCmp collation.compare where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := Value.compare)
  isLE_trans := Std.TransCmp.isLE_trans (cmp := Value.compare)

/-- Whether an ordering satisfies the operator, for operands that are not NULL. -/
def Comparison.holds : Comparison → Ordering → Bool
  | .eq, order | .is, order => order == .eq
  | .ne, order | .isNot, order => order != .eq
  | .lt, order => order == .lt
  | .le, order => order != .gt
  | .gt, order => order == .gt
  | .ge, order => order != .lt

/-- A truth value as SQLite gives it: the integer 1 or 0. -/
def truth (holds : Bool) : Value := .integer (if holds then 1 else 0)

/-- The value of a comparison of two values, after affinity is applied, under a collation
({name}`Collation.compare`, {lit}`BINARY` when none is given). The six ordinary operators give
NULL when an operand is NULL. {lit}`IS` is true for two NULLs and false for one; {lit}`IS NOT`
is its negation. -/
def Comparison.apply (operator : Comparison) (left right : Value) (collation : Collation := .binary) : Value :=
  match operator with
  | .is | .isNot =>
    if left.isNull || right.isNull then truth ((left.isNull && right.isNull) == (operator == .is))
    else truth (operator.holds (collation.compare left right))
  | .eq | .ne | .lt | .le | .gt | .ge =>
    if left.isNull || right.isNull then .null else truth (operator.holds (collation.compare left right))

end Belay.Sqlite.Model
