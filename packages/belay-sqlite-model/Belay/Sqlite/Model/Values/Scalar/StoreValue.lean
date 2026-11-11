import Belay.Sqlite.Model.Values.Scalar.Arithmetic
import Belay.Sqlite.Model.Shared.Values.StoreValue

set_option doc.verso true

/-! Store-time affinity (ADR 0012, amendment 1, "Store-time affinity"): the value that
SQLite stores when it writes a value to a column of an affinity, as SQLite reads it
back. A port of {lit}`applyAffinity`, {lit}`applyNumericAffinity`, {lit}`alsoAnInt` and
{lit}`sqlite3VdbeIntegerAffinity` of the pinned 3.51.0 source, with the read of a REAL
column ({lit}`OP_RealAffinity`). This is not {lit}`castValue`: affinity converts only
when no information is lost, so {lit}`'abc'` stays TEXT in an INTEGER column. -/

namespace Belay.Sqlite.Model

/-- SQLite's {lit}`alsoAnInt` for text with the integer form and the double
{lit}`double`: the integer when the double is the same as its 64-bit integer
({name}`realSameAsInt`), or else when the whole text reads as a 64-bit integer
({name}`atoi64` with code 0); otherwise none. -/
def alsoAnInt (bytes : List UInt8) (double : Float) : Option Int :=
  let whole := realToI64 double
  if realSameAsInt double whole then some whole
  else match atoi64 bytes with
    | (value, 0) => some value
    | _ => none

/-- The number of SQLite's {lit}`applyNumericAffinity` with {lit}`bTryForInt` for text:
none when the text is not a well-formed number ({name}`atof` code 0 or less); for the
integer form, the integer of {name}`alsoAnInt` when there is one; for any other number,
the REAL that {name}`atof` reads, made an integer by {name}`integerAffinity` when it is
whole. -/
def textNumber (bytes : List UInt8) : Option Value :=
  let (double, code) := atof bytes
  if code ≤ 0 then none
  else match (if code == 1 then alsoAnInt bytes double else none) with
    | some whole => some (.integer whole)
    | none => some (integerAffinity double.toBits)

/-- SQLite's {lit}`applyNumericAffinity` with {lit}`bTryForInt` on TEXT: the number of
{name}`textNumber`, or the same TEXT when the text is not a number.
{assert}`numericText [97, 98, 99] = .text [97, 98, 99]`. -/
def numericText (bytes : List UInt8) : Value := (textNumber bytes).getD (.text bytes)

/-- The store of SQLite's NUMERIC and INTEGER affinity ({lit}`applyAffinity` for
{lit}`SQLITE_AFF_NUMERIC` and {lit}`SQLITE_AFF_INTEGER`, which act the same): an integer
stays; a REAL becomes an integer by {name}`integerAffinity` when it is whole; TEXT goes
through {name}`numericText`; NULL and BLOB stay. -/
def numericStore : Value → Value
  | .real bits => integerAffinity bits
  | .text bytes => numericText bytes
  | value@(.null) | value@(.integer _) | value@(.blob _) => value

/-- The value that SQLite stores for a column of the affinity, as it reads it back
(R-54378-38553, R-25142-32967, R-15334-58407, R-12079-51392, R-18885-42713,
R-03366-15091):
* BLOB keeps every value.
* TEXT makes an INTEGER or REAL into its text, with 15 significant digits for a REAL
  ({name}`Value.textBytes`); NULL, TEXT and BLOB stay.
* NUMERIC and INTEGER apply {name}`numericStore`.
* REAL applies {name}`numericStore` to a non-REAL value and then {name}`realRead`. A REAL keeps its bits, except that {lit}`-0.0` becomes {lit}`+0.0`: SQLite
  writes a whole REAL as its integer and reads the integer back as the same double,
  which for a zero is {lit}`+0.0`. Every REAL result goes through {name}`positiveZero`.

{assert}`Value.store .integer (.text [49, 50]) = .integer 12`. Use
{name}`Affinity.blob` for a column without affinity: it changes no value. -/
def Value.store (affinity : Affinity) (value : Value) : Value :=
  match affinity, value with
  | .blob, value => value
  | .text, .integer _ | .text, .real _ => .text value.textBytes
  | .text, value@(.null) | .text, value@(.text _) | .text, value@(.blob _) => value
  | .numeric, value | .integer, value => numericStore value
  | .real, .real bits => .real (positiveZero bits)
  | .real, value@(.null) | .real, value@(.integer _) | .real, value@(.text _) | .real, value@(.blob _) =>
    realRead (numericStore value)

end Belay.Sqlite.Model
