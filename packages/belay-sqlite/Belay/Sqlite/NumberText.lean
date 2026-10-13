import Belay.Sqlite.Declarations

set_option doc.verso true

/-! SQLite's conversions from text to numbers (ADR 0012, slice 2), ported step by step
from the pinned 3.51.0 source: {lit}`sqlite3AtoF`, {lit}`sqlite3Atoi64` and
{lit}`sqlite3RealToI64`. SQLite's text-to-REAL conversion is not correctly rounded: it
multiplies by powers of ten in double-double arithmetic (Dekker). A correctly rounded
parse can give another double, so the model follows SQLite's steps. The text is UTF-8
bytes, as SQLite stores it. The kernel evaluates {lit}`Float`, so conformance proofs
can run these conversions. -/

namespace Belay.Sqlite

/-- Whether a byte is a space for SQLite ({lit}`sqlite3Isspace`): space, tab, line
feed, vertical tab, form feed or carriage return. -/
def isSpaceByte (byte : UInt8) : Bool := byte == 32 || (9 ≤ byte && byte ≤ 13)

/-- Whether a byte is an ASCII digit. -/
def isDigitByte (byte : UInt8) : Bool := 48 ≤ byte && byte ≤ 57

/-- The value of an ASCII digit byte. -/
def digitValue (byte : UInt8) : Nat := (byte - 48).toNat

/-- A double with the low 26 bits of its significand cleared: the high half of the
Dekker split. -/
def dekkerHigh (value : Float) : Float := Float.ofBits (value.toBits &&& 0xfffffffffc000000)

/-- One Dekker step ({lit}`dekkerMul2`): multiply the double-double {lit}`x` by the
double-double {lit}`(y, yy)`, keeping the error term. -/
def dekkerMul2 (x : Float × Float) (y yy : Float) : Float × Float :=
  let hx := dekkerHigh x.1
  let tx := x.1 - hx
  let hy := dekkerHigh y
  let ty := y - hy
  let p := hx * hy
  let q := hx * ty + tx * hy
  let c := p + q
  let cc := p - c + q + tx * ty
  let cc := x.1 * yy + x.2 * y + cc
  let high := c + cc
  (high, c - high + cc)

/-- Apply {lit}`dekkerMul2` with the factor {lit}`(y, yy)` while the exponent is at least
{lit}`step`, lowering it by {lit}`step` each time; the fuel bounds the steps. -/
def scaleDown (fuel step : Nat) (y yy : Float) : Float × Float → Nat → (Float × Float) × Nat
  | x, exponent => match fuel with
    | 0 => (x, exponent)
    | fuel + 1 => if step ≤ exponent then scaleDown fuel step y yy (dekkerMul2 x y yy) (exponent - step)
      else (x, exponent)

/-- The parse state of {lit}`sqlite3AtoF`: significand, decimal shift, exponent and its
sign, whether the exponent is well formed, digit count and the number kind (1 for an
integer, 2 or more with a fraction or exponent). -/
structure AtofState where
  /-- The significand, below {lit}`2^64`. -/
  significand : Nat := 0
  /-- The decimal shift from digits that the significand dropped or the fraction added. -/
  shift : Int := 0
  /-- The written exponent, at most 10000. -/
  exponent : Nat := 0
  /-- Whether the exponent is negative. -/
  negativeExponent : Bool := false
  /-- Whether an exponent, if written, has digits. -/
  exponentValid : Bool := true
  /-- The number of significand digits read. -/
  digits : Nat := 0
  /-- 1 for an integer form, 2 or more with a fraction or an exponent. -/
  kind : Nat := 1

/-- The significand limit of {lit}`sqlite3AtoF`: {lit}`(LARGEST_UINT64 - 9) / 10`. -/
def atofLimit : Nat := (2 ^ 64 - 1 - 9) / 10

/-- Read integer digits into the significand; past the limit, count them as shift. -/
def atofInteger (state : AtofState) : List UInt8 → AtofState × List UInt8
  | byte :: rest =>
    if isDigitByte byte then
      if state.significand ≥ atofLimit then atofInteger { state with shift := state.shift + 1 } rest
      else atofInteger { state with significand := state.significand * 10 + digitValue byte,
                                    digits := state.digits + 1 } rest
    else (state, byte :: rest)
  | [] => (state, [])

/-- Read fraction digits; past the limit, ignore them. -/
def atofFraction (state : AtofState) : List UInt8 → AtofState × List UInt8
  | byte :: rest =>
    if isDigitByte byte then
      if state.significand < atofLimit then
        atofFraction { state with significand := state.significand * 10 + digitValue byte,
                                  shift := state.shift - 1, digits := state.digits + 1 } rest
      else atofFraction state rest
    else (state, byte :: rest)
  | [] => (state, [])

/-- Read exponent digits; the exponent stops growing at 10000. -/
def atofExponent (state : AtofState) : List UInt8 → AtofState × List UInt8
  | byte :: rest =>
    if isDigitByte byte then
      atofExponent { state with exponent := if state.exponent < 10000 then state.exponent * 10 + digitValue byte
                                             else 10000, exponentValid := true } rest
    else (state, byte :: rest)
  | [] => (state, [])

/-- The text after leading spaces. -/
def dropSpaces (bytes : List UInt8) : List UInt8 := bytes.dropWhile isSpaceByte

/-- The optional sign at the start of a number: {lit}`-1` after a minus, else 1, and
the text after it. -/
def readSign : List UInt8 → Int × List UInt8
  | 45 :: rest => (-1, rest)
  | 43 :: rest => (1, rest)
  | bytes => (1, bytes)

/-- The parse of {lit}`sqlite3AtoF`, after leading spaces: the sign, the state and the
text that is left after trailing spaces. {lit}`none` stands for empty
text, which converts to zero. -/
def atofParse (bytes : List UInt8) : Option (Int × AtofState × List UInt8) :=
  match dropSpaces bytes with
  | [] => none
  | text =>
    let (sign, text) := readSign text
    let (state, text) := atofInteger {} text
    match text with
    | [] => some (sign, state, [])
    | 46 :: fraction =>
      let (state, text) := atofFraction { state with kind := state.kind + 1 } fraction
      some (sign, exponentPart state text)
    | text => some (sign, exponentPart state text)
where
  /-- The exponent part, if any, then the trailing spaces. -/
  exponentPart (state : AtofState) : List UInt8 → AtofState × List UInt8
    | [] => (state, [])
    | marker :: rest =>
      if marker == 101 || marker == 69 then
        let state := { state with exponentValid := false, kind := state.kind + 1 }
        match rest with
        | [] => (state, [])
        | rest =>
          let (exponentSign, rest) := readSign rest
          let (state, rest) := atofExponent { state with negativeExponent := exponentSign < 0 } rest
          (state, dropSpaces rest)
      else (state, dropSpaces (marker :: rest))

end Belay.Sqlite
