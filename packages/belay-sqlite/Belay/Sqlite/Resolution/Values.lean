import Belay.Sqlite.Resolution.Profile
import Belay.Sqlite.Resolution.Resolved
import Belay.Sqlite.NumberConvert
import Belay.Sqlite.Arithmetic

set_option doc.verso true

/-! Conversion of literal expressions to stored values during name resolution.
Numeric literal text follows SQLite's rules, which are not lexical: separators are
removed, a hexadecimal literal is a 64-bit two's-complement integer, and a decimal
integer outside the 64-bit range is a REAL value. The first scope models no REAL
values and no time functions, so those are model restrictions. -/

namespace Belay.Sqlite

/-- Why an expression has no value: a SQLite prepare error, or a model restriction
with the path of the node inside the expression. -/
inductive ValueIssue where
  /-- SQLite refuses to prepare the statement. -/
  | prepare (error : PrepareError)
  /-- The model does not describe the expression at this path, for the reason of the
  restriction kind. -/
  | restriction (path : List Nat) (kind : RestrictionKind)
  deriving Repr, DecidableEq

/-- Prefix the paths of model restrictions with the node's position. -/
def ValueIssue.under (prefix_ : List Nat) : ValueIssue → ValueIssue
  | .restriction path reason => .restriction (prefix_ ++ path) reason
  | .prepare error => .prepare error

/-- The value of a numeric literal's text: an integer, a REAL value that the first
scope does not model, or a hexadecimal literal too large for 64 bits. -/
inductive NumericValue where
  /-- A signed 64-bit integer. -/
  | integer (value : Int)
  /-- A REAL value. -/
  | real
  /-- More than 16 hexadecimal digits: {lit}`hex literal too big: %s`. -/
  | hexTooBig
  deriving Repr, DecidableEq

/-- The value of a hexadecimal digit, or {lean}`(none : Option Nat)`. -/
def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The value of digits in a base, or {lean}`(none : Option Nat)` for an
empty list or a character that is not a digit of that base. -/
def digitsValue (base : Nat) (digits : List Char) : Option Nat :=
  if digits.isEmpty then none else
  digits.foldl (fun result c => do
    let value ← result
    let digit ← hexDigit c
    if digit < base then some (value * base + digit) else none) (some 0)

/-- Whether an integer is in SQLite's signed 64-bit range. -/
def fitsInt64 (value : Int) : Bool := decide (-(2 ^ 63 : Int) ≤ value ∧ value < 2 ^ 63)

/-- A decimal integer times the sign, when it fits in 64 bits; REAL for a larger
integer or for any other numeric text. -/
def decimalNumericValue (chars : List Char) (sign : Int) : NumericValue :=
  match digitsValue 10 chars with
  | some value => if fitsInt64 (sign * value) then .integer (sign * value) else .real
  | none => .real

/-- SQLite's value of a numeric literal token, negated when {lit}`negated` is
true. Underscore separators are removed first. A literal with 1 to 16 hexadecimal
digits after {lit}`0x` is the 64-bit two's-complement integer of those bits; more
digits are {name}`NumericValue.hexTooBig`. A decimal integer is an integer when
it fits in 64 bits after negation, so {lit}`-9223372036854775808` is an integer;
otherwise it is REAL. A literal with a decimal point or an exponent is REAL. -/
def numericValue (text : String) (negated : Bool) : NumericValue :=
  let chars := text.toList.filter (· ≠ '_')
  let sign : Int := if negated then -1 else 1
  match chars with
  | '0' :: x :: hex =>
    if x = 'x' ∨ x = 'X' then
      if hex.length > 16 then .hexTooBig else
      match digitsValue 16 hex with
      | some bits =>
        let signed : Int := if bits ≥ 2 ^ 63 then bits - 2 ^ 64 else bits
        if fitsInt64 (sign * signed) then .integer (sign * signed) else .real
      | none => .real
    else decimalNumericValue chars sign
  | _ => decimalNumericValue chars sign

/-- The text of SQLite's {lit}`hex literal too big` error: the literal as written, after
a minus sign when it is negated ({lit}`codeInteger`). -/
def hexErrorText (text : String) (negated : Bool) : String := (if negated then "-" else "") ++ text

/-- Whether literal characters, without separators, start with {lit}`0x` or {lit}`0X`. -/
def startsHex (chars : List Char) : Bool := chars.take 2 == ['0', 'x'] || chars.take 2 == ['0', 'X']

/-- The REAL value of a numeric literal's characters without separators
({lit}`codeReal`): {name}`atof` of the text, negated when {lit}`negated` is true. -/
def realLiteral (chars : List Char) (negated : Bool) : Value :=
  let value := (atof (String.ofList chars).toUTF8.toList).1
  realValue (if negated then -value else value)

/-- The value of a numeric literal in a query ({lit}`codeInteger` and {lit}`codeReal`):
an integer as in {name}`numericValue`; a REAL by {name}`realLiteral`; and the
{lit}`hex literal too big` error for a hexadecimal literal outside 64 bits, also
after negation. -/
def queryNumeric (text : String) (negated : Bool) : Except ValueIssue Value :=
  let chars := text.toList.filter (· ≠ '_')
  match numericValue text negated, startsHex chars with
  | .integer value, _ => .ok (.integer value)
  | .hexTooBig, _ | .real, true => .error (.prepare (.hexLiteralTooBig (hexErrorText text negated)))
  | .real, false => .ok (realLiteral chars negated)

end Belay.Sqlite
