import Belay.Sqlite.Model.Declarations
import Belay.Sqlite.Model.Operators

set_option doc.verso true

/-! The Values level of ADR 0012: SQLite's comparison of two stored values, as
"Comparison Expressions" and "Sort Order" of the pinned {lit}`datatype3.html`
state it. Each value maps to a sort key of three parts, compared in order: the
storage class, the exact number, and the bytes. -/

namespace Belay.Sqlite.Model

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
def Value.compare : Value → Value → Ordering :=
  compareLex (compareOn Value.rank) (compareLex (compareOn Value.scaled) (compareOn Value.bytes))

/-- For all values, {name}`Value.compare` is a transitive, oriented comparison: a total
preorder, as a sort and a grouping need. The proof is the core instance for a
lexicographic combination of keyed comparisons. -/
instance : Std.TransCmp Value.compare := by
  unfold Value.compare; exact inferInstance


/-- For every value of nonzero rank ({name}`Value.rank`), NULL comes before it in
{name}`Value.compare`. Rank 0 holds NULL and also a NaN REAL, which the model never makes and
which compares equal to NULL. -/
theorem Value.compare_null (value : Value) (ranked : value.rank ≠ 0) : Value.compare .null value = .lt := by
  have before : Ord.compare (0 : Nat) value.rank = .lt := Nat.compare_eq_lt.mpr (Nat.pos_of_ne_zero ranked)
  have null : Value.rank .null = 0 := rfl
  simp only [Value.compare, compareLex, compareOn, null, before, Ordering.then]

/-- A collating sequence of SQLite (ADR 0014, D3): how TEXT values compare. {lit}`BINARY`
compares bytes, {lit}`NOCASE` compares with ASCII letters folded, and {lit}`RTRIM` compares
without trailing spaces. Values of other storage classes compare the same under each. Use
{lean}`Collation.binary` where SQLite names no collation. -/
inductive Collation where
  /-- {lit}`BINARY`: the bytes. -/
  | binary
  /-- {lit}`NOCASE`: the bytes with ASCII capitals folded to lowercase. -/
  | nocase
  /-- {lit}`RTRIM`: the bytes without trailing spaces. -/
  | rtrim
  deriving Repr, DecidableEq

/-- The built-in collation that a name names, with ASCII case ignored: {lit}`BINARY`,
{lit}`NOCASE` or {lit}`RTRIM`; none for any other name, which SQLite refuses with
{lit}`no such collation sequence`. -/
def Collation.named? (name : Identifier) : Option Collation :=
  if name.isKeyword (bytes! "binary") then some .binary
  else if name.isKeyword (bytes! "nocase") then some .nocase
  else if name.isKeyword (bytes! "rtrim") then some .rtrim
  else none

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
