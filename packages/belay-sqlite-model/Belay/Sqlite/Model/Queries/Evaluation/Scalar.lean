import Belay.Sqlite.Model.Queries.Evaluation.Arithmetic
import Belay.Sqlite.Model.Queries.Evaluation.Comparison
import Belay.Sqlite.Model.Values.Scalar.Scalar

set_option doc.verso true

/-! The values of the scalar functions of ADR 0015 over their argument values, as SQLite
3.51.0's {lit}`func.c` computes them. A failure that SQLite reports while the statement runs
is the failure {lit}`error`; a value that the model does not describe is {lit}`unmodeled`. {lit}`iif` is lazy, so
expression evaluation computes it, and {lit}`apply` gives it NULL. A number of arguments that
the catalog does not accept gives NULL. -/

namespace Belay.Sqlite.Model.Resolved

/-- The value of a scalar function over its argument values, or its failure. The number of
arguments is the one that resolution checked against the catalog; another number gives
NULL.
* {lit}`typeof` is {name}`typeName`; {lit}`length` counts {name}`utf8Length` for text, and the
  bytes of a BLOB or of the text of a number; {lit}`octet_length` counts bytes.
* {lit}`abs` of an integer is its magnitude, and of the smallest integer
  {name}`FunctionFailure.error`; of any other value but NULL the magnitude of its double.
* {lit}`sign` is the sign of a number, also of text that reads as a number, else NULL.
* {lit}`zeroblob` makes zero bytes, none for a negative size.
* {lit}`nullif` is NULL when its arguments compare equal under the collation.
* {lit}`min` replaces the best argument unless the best is less ({lit}`mask` 0 of
  {lit}`minmaxFunc`), {lit}`max` only when the best is less. -/
def ScalarFunction.apply : ScalarFunction → List Value → Except FunctionFailure Value
  | .typeof, [value] => .ok (.text (typeName value))
  | .length, [value] => .ok (match value with
    | .text bytes => .integer (utf8Length bytes)
    | .blob bytes => .integer bytes.length
    | .integer _ | .real _ => .integer value.textBytes.length
    | .null => .null)
  | .octetLength, [value] => .ok (match value with
    | .null => .null
    | .text _ | .blob _ | .integer _ | .real _ => .integer value.textBytes.length)
  | .abs, [value] => match value with
    | .integer integer =>
      if integer == -(2 ^ 63) then .error .error else .ok (.integer (if integer < 0 then -integer else integer))
    | .null => .ok .null
    | .real _ | .text _ | .blob _ =>
      let double := value.toReal
      .ok (realValue (if double < 0 then -double else double))
  | .sign, [value] =>
    let number := match value with
      | .text bytes => numericText bytes
      | .null | .integer _ | .real _ | .blob _ => value
    .ok (match number with
      | .integer integer => .integer (if integer < 0 then -1 else if 0 < integer then 1 else 0)
      | .real bits =>
        let double := Float.ofBits bits
        .integer (if double < 0 then -1 else if 0 < double then 1 else 0)
      | .text _ | .blob _ | .null => .null)
  | .zeroblob, [size] =>
    let count := if size.toInt64 < 0 then 0 else size.toInt64
    if zeroblobLimit < count then .error .unmodeled else .ok (.blob (List.replicate count.toNat 0))
  | .nullif collation, [left, right] => .ok (if collation.compare left right == .eq then .null else left)
  | .min collation, first :: rest =>
    .ok (if first.isNull then .null else bestArgument (fun best argument => collation.compare best argument != .lt) first rest)
  | .max collation, first :: rest =>
    .ok (if first.isNull then .null else bestArgument (fun best argument => collation.compare best argument == .lt) first rest)
  | .like, [pattern, string] => likeResult likeDialect pattern string none
  | .like, [pattern, string, escape] => likeResult likeDialect pattern string (some escape)
  | .glob, [pattern, string] => likeResult globDialect pattern string none
  | .lower, [value] => .ok (mapText lowerByte value)
  | .upper, [value] => .ok (mapText upperByte value)
  | .substr, [value, start] => .ok (substrValue value start none)
  | .substr, [value, start, count] => .ok (substrValue value start (some count))
  | .instr, [haystack, needle] => .ok (instrValue haystack needle)
  | .replace, [value, pattern, replacement] => .ok (replaceValue value pattern replacement)
  | .trim side, [value] => .ok (trimValue side value none)
  | .trim side, [value, characters] => .ok (trimValue side value (some characters))
  | .hex, [value] => .ok (hexValue value)
  | .unhex, [value] => .ok (unhexValue value none)
  | .unhex, [value, ignored] => .ok (unhexValue value (some ignored))
  | .quote, [value] => .ok (quoteValue false value)
  | .unistrQuote, [value] => .ok (quoteValue true value)
  | .char, values => .ok (charValue values)
  | .unicode, [value] => .ok (unicodeValue value)
  | .unistr, [value] => match unistrValue value with
    | some result => .ok result
    | none => .error .error
  | .concat, values => .ok (concatValue [] values)
  | .pipes, [left, right] => .ok (if left.isNull || right.isNull then .null else .text (left.textBytes ++ right.textBytes))
  | .concatWs, separator :: values => .ok (if separator.isNull then .null else concatValue separator.textBytes values)
  | .round, [value] => .ok (roundValue value none)
  | .round, [value, digits] => .ok (roundValue value (some digits))
  | .floor, [value] => .ok (roundingValue floorDouble value)
  | .ceil, [value] => .ok (roundingValue ceilDouble value)
  | .trunc, [value] => .ok (roundingValue truncDouble value)
  | .sqrt, [value] => .ok (doubleValue Float.sqrt value)
  | .pi, [] => .ok (realValue piDouble)
  | .degrees, [value] => .ok (doubleValue (· * ((180.0 : Float) / piDouble)) value)
  | .radians, [value] => .ok (doubleValue (· * (piDouble / (180.0 : Float))) value)
  | .mod, [x, y] => .ok (modValue x y)
  | .printf, values => printfValue values
  | .round, _ | .floor, _ | .ceil, _ | .trunc, _ | .sqrt, _ | .pi, _ | .degrees, _ | .radians, _ | .mod, _
  | .typeof, _ | .length, _ | .octetLength, _ | .abs, _ | .sign, _ | .zeroblob, _ | .iif, _ | .nullif _, _
  | .min _, _ | .max _, _ | .like, _ | .glob, _ | .lower, _ | .upper, _ | .substr, _ | .instr, _ | .replace, _
  | .trim _, _ | .hex, _ | .unhex, _ | .quote, _ | .unistrQuote, _ | .unicode, _ | .unistr, _ | .concatWs, _ | .pipes, _ =>
    .ok .null

/-- For every scalar function that cannot fail ({name}`ScalarFunction.canFail` is false) and
all argument values, {name}`ScalarFunction.apply` gives a value. Proof sketch: split on the
function, which leaves the functions that cannot fail, and on the case of
{name}`ScalarFunction.apply` for the argument list; each case of these functions is a value. -/
theorem ScalarFunction.apply_ok (function : ScalarFunction) (values : List Value)
    (safe : function.canFail = false) : ∃ value, function.apply values = .ok value := by
  cases function <;> simp [ScalarFunction.canFail] at safe <;> unfold ScalarFunction.apply <;> split <;>
    first | exact ⟨_, rfl⟩ | simp_all

end Belay.Sqlite.Model.Resolved
