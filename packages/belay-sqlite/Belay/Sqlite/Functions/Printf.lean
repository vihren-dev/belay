import Belay.Sqlite.Functions.PrintfText
import Belay.Sqlite.Functions.Failure

set_option doc.verso true

/-! The SQL functions {lit}`printf` and {lit}`format` (ADR 0015, slice 6): SQLite 3.51.0's
{lit}`printfFunc`, which runs {lit}`sqlite3_str_vappendf` over the format text with the other
arguments as the values of its fields ({lit}`SQLITE_PRINTF_SQLFUNC`). A field reads the next
argument, or 0, 0.0 or no text when the arguments are used up. An unknown conversion, and the
internal conversions {lit}`%T` and {lit}`%S`, end the output. -/

namespace Belay.Sqlite.Resolved

/-- The largest width or precision that the model writes: 100000. A larger one is
{name}`FunctionFailure.unmodeled`, so that a proof never builds a long list. -/
def printfFieldLimit : Nat := 100000

/-- The next argument as an integer ({lit}`getIntArg`: {lit}`sqlite3_value_int64`, 0 when none
is left), and the arguments after it. -/
def nextInteger : List Value → Int × List Value
  | [] => (0, [])
  | value :: rest => (value.toInt64, rest)

/-- An integer as the C {lit}`int` that {lit}`(int)getIntArg(...)` gives: its low 32 bits, signed. -/
def toInt32 (value : Int) : Int :=
  let low := value % 2 ^ 32
  if low ≥ 2 ^ 31 then low - 2 ^ 32 else low

/-- The decimal digits from {lit}`position`: their value modulo 2^32 as {lit}`unsigned`
accumulates it, and the position after them. -/
def readDigits (format : Array UInt8) : Nat → Nat → Nat → Nat × Nat
  | 0, position, value => (value, position)
  | fuel + 1, position, value =>
    let byte := format.getD position 0
    if 48 ≤ byte && byte ≤ 57 then readDigits format fuel (position + 1) ((value * 10 + (byte - 48).toNat) % 2 ^ 32)
    else (value, position)

/-- The flags, width and precision of a field from {lit}`position` (the flag loop of
{lit}`sqlite3_str_vappendf`): the field, its conversion byte (0 at the end of the format), the
position of that byte, and the arguments after those that {lit}`*` read. -/
def parseField (format : Array UInt8) : Nat → Nat → PrintfSpec → List Value → PrintfSpec × UInt8 × Nat × List Value
  | 0, position, spec, arguments => (spec, 0, position, arguments)
  | fuel + 1, position, spec, arguments =>
    let byte := format.getD position 0
    let next := fun (spec : PrintfSpec) => parseField format fuel (position + 1) spec arguments
    if byte == 45 then next { spec with leftJustify := Bool.true }
    else if byte == 43 || byte == 32 then next { spec with signFlag := byte }
    else if byte == 35 then next { spec with alternate := Bool.true }
    else if byte == 33 then next { spec with bang := Bool.true }
    else if byte == 48 then next { spec with zeroPad := Bool.true }
    else if byte == 44 then next { spec with thousands := Bool.true }
    else if byte == 108 then
      let position := if format.getD (position + 1) 0 == 108 then position + 2 else position + 1
      (spec, format.getD position 0, position, arguments)
    else if 49 ≤ byte && byte ≤ 57 then
      let (width, after) := readDigits format format.size position 0
      let spec := { spec with width := width % 2 ^ 31 }
      let following := format.getD after 0
      if following != 46 && following != 108 then (spec, following, after, arguments)
      else parseField format fuel after spec arguments
    else if byte == 42 then
      let (value, arguments) := nextInteger arguments
      let width := toInt32 value
      let spec := if width < 0 then
          { spec with leftJustify := Bool.true, width := if width ≥ -2147483647 then (-width).toNat else 0 }
        else { spec with width := width.toNat }
      let following := format.getD (position + 1) 0
      if following != 46 && following != 108 then (spec, following, position + 1, arguments)
      else parseField format fuel (position + 1) spec arguments
    else if byte == 46 then
      let (spec, after, arguments) :=
        if format.getD (position + 1) 0 == 42 then
          let (value, arguments) := nextInteger arguments
          let precision := toInt32 value
          ({ spec with precision := if precision ≥ 0 then some precision.toNat
              else if precision ≥ -2147483647 then some (-precision).toNat else none }, position + 2, arguments)
        else
          let (precision, after) := readDigits format format.size (position + 1) 0
          ({ spec with precision := some (precision % 2 ^ 31) }, after, arguments)
      let following := format.getD after 0
      if following == 108 then parseField format fuel after spec arguments else (spec, following, after, arguments)
    else (spec, byte, position, arguments)

/-- The text of one field of conversion {lit}`conversion` over the next argument, with the
arguments after it, or none for a conversion that ends the output. -/
def fieldText (spec : PrintfSpec) (conversion : UInt8) (arguments : List Value) : Option (List UInt8 × List Value) :=
  let (argument, rest) : Option Value × List Value := match arguments with
    | [] => (none, [])
    | value :: rest => (some value, rest)
  let integer := (argument.map Value.toInt64).getD 0
  let double := (argument.map Value.toReal).getD 0
  let text := argument.bind cText?
  let number := fun (form : IntegerForm) =>
    some (padField spec.leftJustify spec.width (integerField spec form integer), rest)
  let real := fun (form : DoubleForm) (upper : Bool) =>
    some (padField spec.leftJustify spec.width (doubleField spec form upper double), rest)
  match conversion.toNat with
  | 100 | 105 => number ⟨10, Bool.true, Bool.false, Bool.false, [], Bool.true⟩
  | 117 => number ⟨10, Bool.false, Bool.false, Bool.false, [], Bool.true⟩
  | 114 => number ⟨10, Bool.true, Bool.false, Bool.true, [], Bool.false⟩
  | 120 => number ⟨16, Bool.false, Bool.false, Bool.false, [48, 120], Bool.false⟩
  | 88 => number ⟨16, Bool.false, Bool.true, Bool.false, [48, 88], Bool.false⟩
  | 111 => number ⟨8, Bool.false, Bool.false, Bool.false, [48], Bool.false⟩
  | 112 => number ⟨16, Bool.false, Bool.true, Bool.false, [48, 120], Bool.false⟩
  | 102 => real .fixed Bool.false
  | 101 => real .exponent Bool.false
  | 69 => real .exponent Bool.true
  | 103 => real .general Bool.false
  | 71 => real .general Bool.true
  | 115 | 122 => some (stringField spec text, rest)
  | 99 => some (charField spec text, rest)
  | 113 => some (escapeField spec Bool.false Bool.false text, rest)
  | 81 => some (escapeField spec Bool.true Bool.false text, rest)
  | 119 => some (escapeField spec Bool.false Bool.true text, rest)
  | 37 => some (padField spec.leftJustify spec.width [37], arguments)
  | 110 => some ([], arguments)
  | _ => none

/-- The output of the format from {lit}`position` ({lit}`sqlite3_str_vappendf`): the bytes up to
the next {lit}`%`, a lone {lit}`%` at the end as itself, then each field; a width or precision
above {name}`printfFieldLimit` is {name}`FunctionFailure.unmodeled`. -/
def printfFrom (format : Array UInt8) : Nat → Nat → List Value → Except FunctionFailure (List UInt8)
  | 0, _, _ => .ok []
  | fuel + 1, position, arguments =>
    if position ≥ format.size then .ok []
    else if format.getD position 0 != 37 then
      (printfFrom format fuel (position + 1) arguments).map (format.getD position 0 :: ·)
    else if position + 1 ≥ format.size then .ok [37]
    else
      let (spec, conversion, place, arguments) := parseField format format.size (position + 1) {} arguments
      if spec.width > printfFieldLimit || spec.precision.any (· > printfFieldLimit) then .error .unmodeled
      else match fieldText spec conversion arguments with
        | none => .ok []
        | some (field, arguments) => (printfFrom format fuel (place + 1) arguments).map (field ++ ·)

/-- {lit}`printf(format, ...)` and {lit}`format(format, ...)`: NULL without arguments or for a
NULL format, else the TEXT of {name}`printfFrom` over the format's text up to its first NUL
byte. For example {lit}`printf('%5.2f|%-3d|%s', 3.14159, 7, 'x')` is {lit}`' 3.14|7  |x'`. -/
def printfValue : List Value → Except FunctionFailure Value
  | [] => .ok .null
  | format :: arguments => match cText? format with
    | none => .ok .null
    | some bytes => (printfFrom bytes.toArray (bytes.length + 1) 0 arguments).map Value.text

end Belay.Sqlite.Resolved
