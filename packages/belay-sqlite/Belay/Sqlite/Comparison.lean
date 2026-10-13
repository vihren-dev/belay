import Belay.Sqlite.Declarations

set_option doc.verso true

/-! The Values level of ADR 0012: SQLite's comparison of two stored values, as
"Comparison Expressions" and "Sort Order" of the pinned {lit}`datatype3.html`
state it. Each value maps to a sort key of three parts, compared in order: the
storage class, the exact number, and the bytes. -/

namespace Belay.Sqlite

/-- The exact number of a REAL value's IEEE 754 bits, times {lit}`2^1074`, so that
every finite double is an integer and compares exactly with an integer value
times the same factor. Infinities are {lit}`±2^2200`, beyond every finite double.
{lean}`(none : Option Int)` for a NaN bit pattern. -/
def realScaled (bits : UInt64) : Option Int :=
  let sign : Int := if bits >>> 63 = 1 then -1 else 1
  let exponent := ((bits >>> 52) &&& 0x7FF).toNat
  let fraction := (bits &&& 0xFFFFFFFFFFFFF).toNat
  if exponent = 0x7FF then (if fraction = 0 then some (sign * 2 ^ 2200) else none)
  else if exponent = 0 then some (sign * fraction)
  else some (sign * ((2 ^ 52 + fraction) * 2 ^ (exponent - 1)))

/-- The storage class order of SQLite: NULL is less than every other value
(R-08551-61977), a number is less than any TEXT or BLOB (R-14505-63184), and a TEXT
is less than a BLOB (R-64324-28127). A NaN REAL ranks as NULL, because SQLite
stores a NaN as NULL. -/
def Value.rank : Value → Nat
  | .null => 0
  | .integer _ => 1
  | .real bits => if (realScaled bits).isSome then 1 else 0
  | .text _ => 2
  | .blob _ => 3

/-- The exact number of a numeric value times {lit}`2^1074`; zero for other values.
An integer and a REAL with the same mathematical value have the same number. -/
def Value.scaled : Value → Int
  | .integer value => value * 2 ^ 1074
  | .real bits => (realScaled bits).getD 0
  | .null | .text _ | .blob _ => 0

/-- The bytes of a TEXT or BLOB value; empty for other values. Bytes compare as
{lit}`memcmp` does, which is SQLite's BINARY collation (R-53528-47027). -/
def Value.bytes : Value → List UInt8
  | .text bytes | .blob bytes => bytes
  | .null | .integer _ | .real _ => []

/-- SQLite's comparison of two values: by storage class, then numerically, then by
bytes. Two values compare as equal exactly when they are both NULL, or numbers with
the same value, or TEXT or BLOB values with the same bytes. -/
def compareValues : Value → Value → Ordering :=
  compareLex (compareOn Value.rank) (compareLex (compareOn Value.scaled) (compareOn Value.bytes))

/-- For all values, {name}`compareValues` is a transitive, oriented comparison: a total
preorder, as a sort and a grouping need. The proof is the core instance for a
lexicographic combination of keyed comparisons. -/
instance : Std.TransCmp compareValues := by
  unfold compareValues; exact inferInstance

/-- Whether the value is NULL in a comparison: a NULL, or a NaN REAL. -/
def Value.isNull (value : Value) : Bool := value.rank == 0

/-- A comparison operator of SQL: the six that give NULL for a NULL operand, and
{lit}`IS` and {lit}`IS NOT`, which treat two NULLs as equal (R-24731-45773). -/
inductive Comparison where
  /-- {lit}`=` or {lit}`==`. -/
  | eq
  /-- {lit}`<>` or {lit}`!=`. -/
  | ne
  /-- {lit}`<`. -/
  | lt
  /-- {lit}`<=`. -/
  | le
  /-- {lit}`>`. -/
  | gt
  /-- {lit}`>=`. -/
  | ge
  /-- {lit}`IS`. -/
  | is
  /-- {lit}`IS NOT`. -/
  | isNot
  deriving Repr, DecidableEq

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

/-- The value of a comparison of two values, after affinity is applied. The six
ordinary operators give NULL when an operand is NULL. {lit}`IS` is true for two
NULLs and false for one; {lit}`IS NOT` is its negation. -/
def Comparison.apply (operator : Comparison) (left right : Value) : Value :=
  match operator with
  | .is | .isNot =>
    if left.isNull || right.isNull then truth ((left.isNull && right.isNull) == (operator == .is))
    else truth (operator.holds (compareValues left right))
  | .eq | .ne | .lt | .le | .gt | .ge =>
    if left.isNull || right.isNull then .null else truth (operator.holds (compareValues left right))

#guard compareValues (.integer 1) (.real 0x3FF0000000000000) == .eq
#guard compareValues (.integer 9007199254740993) (.real 0x4340000000000001) == .lt
#guard compareValues .null (.integer (-5)) == .lt
#guard compareValues (.real 0xFFF0000000000000) (.integer (-(2 ^ 63))) == .lt
#guard compareValues (.integer 7) (.text []) == .lt
#guard compareValues (.text [255]) (.blob []) == .lt
#guard compareValues (.text [97]) (.text [97, 0]) == .lt
#guard compareValues (.real 0x8000000000000000) (.real 0) == .eq
#guard Comparison.eq.apply .null .null == .null
#guard Comparison.is.apply .null .null == .integer 1
#guard Comparison.isNot.apply .null (.integer 0) == .integer 1

end Belay.Sqlite
