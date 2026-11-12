import Belay.Sqlite.Model.Shared.Values.Declarations
import Belay.Sqlite.Model.Shared.Resolved.Operators

set_option doc.verso true

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

end Belay.Sqlite.Model
