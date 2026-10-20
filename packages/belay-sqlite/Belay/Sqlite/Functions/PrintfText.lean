import Belay.Sqlite.Functions.PrintfNumbers

set_option doc.verso true

/-! The text fields of SQLite's {lit}`printf` (ADR 0015, slice 6): {lit}`%s` and {lit}`%z`,
{lit}`%c`, and the quoting conversions {lit}`%q`, {lit}`%Q` and {lit}`%w`, from the
{lit}`etSTRING`, {lit}`etCHARX` and {lit}`etESCAPE_*` branches of {lit}`sqlite3_str_vappendf` in
SQLite 3.51.0, and the padding of a field to its width. -/

namespace Belay.Sqlite.Resolved

/-- Whether a byte continues a UTF-8 character ({lit}`0x80` to {lit}`0xBF`). -/
def isContinuation (byte : UInt8) : Bool := byte &&& 0xc0 == 0x80

/-- The number of bytes of the first {lit}`count` characters ({lit}`SQLITE_SKIP_UTF8`): a byte
from {lit}`0xC0` takes the continuation bytes after it, and any other byte is one character. -/
def utf8PrefixLength : Nat → List UInt8 → Nat
  | 0, _ | _, [] => 0
  | count + 1, byte :: rest =>
    if byte ≥ 0xc0 then
      let tail := rest.takeWhile isContinuation
      1 + tail.length + utf8PrefixLength count (rest.drop tail.length)
    else 1 + utf8PrefixLength count rest

/-- The width of a field of {lit}`bytes` under the {lit}`!` flag ({lit}`adjust_width_for_utf8`): a
positive width grows by one for each continuation byte, so it counts characters. -/
def utf8Width (bang : Bool) (width : Int) (bytes : List UInt8) : Int :=
  if bang && width > 0 then width + (bytes.filter isContinuation).length else width

/-- A field padded with spaces to its width in bytes: on the left, or on the right under the
{lit}`-` flag. -/
def padField (leftJustify : Bool) (width : Int) (bytes : List UInt8) : List UInt8 :=
  let spaces := List.replicate (width - bytes.length).toNat 32
  if leftJustify then bytes ++ spaces else spaces ++ bytes

/-- A {lit}`%s` field: the text of the argument ({lit}`""` for NULL or a missing argument), cut
to the precision in bytes, or in characters under the {lit}`!` flag, and padded. -/
def stringField (spec : PrintfSpec) (text : Option (List UInt8)) : List UInt8 :=
  let bytes := text.getD []
  let body := match spec.precision with
    | some precision => bytes.take (if spec.bang then utf8PrefixLength precision bytes else precision)
    | none => bytes
  padField spec.leftJustify (utf8Width spec.bang spec.width body) body

/-- A {lit}`%c` field: the first character of the argument's text (a NUL byte for NULL or empty
text), repeated {lit}`precision` times; with a repeat, the width less the extra copies is
padded on the left before them, else after the last copy; the width counts characters. -/
def charField (spec : PrintfSpec) (text : Option (List UInt8)) : List UInt8 :=
  let char := match text.getD [] with
    | [] => [0]
    | first :: rest => first :: (if first &&& 0xc0 == 0xc0 then (rest.takeWhile isContinuation).take 3 else [])
  let precision := spec.precision.getD 0
  let (before, width) : List UInt8 × Int :=
    if precision > 1 then
      let width : Int := (spec.width : Int) - (precision - 1)
      let copies := (List.replicate (precision - 1) char).flatten
      if width > 1 && !spec.leftJustify then (List.replicate (width - 1).toNat 32 ++ copies, 0) else (copies, width)
    else ([], spec.width)
  before ++ padField spec.leftJustify (utf8Width Bool.true width char) char

/-- The bytes of a quoting conversion before its precision ends ({lit}`etESCAPE_q`): up to
{lit}`limit` bytes, or characters under the {lit}`!` flag. -/
def escapedInput (bang : Bool) (limit : Option Nat) (bytes : List UInt8) : List UInt8 :=
  match limit with
  | none => bytes
  | some limit => bytes.take (if bang then utf8PrefixLength limit bytes else limit)

/-- The escaped body of a quoting conversion: the quote byte doubled, and under the {lit}`#`
form a backslash doubled and a control byte as {lit}`\u00XX`. -/
def escapeBody (quote : UInt8) (backslashes : Bool) (bytes : List UInt8) : List UInt8 :=
  bytes.flatMap fun byte =>
    if byte == quote then [byte, byte]
    else if backslashes && byte == 92 then [92, 92]
    else if backslashes && byte ≤ 0x1f then
      [92, 117, 48, 48, if byte ≥ 0x10 then 49 else 48, "0123456789abcdef".toUTF8.toList.getD (byte % 16).toNat 48]
    else [byte]

/-- A quoting field ({lit}`%q`, {lit}`%Q` when {lit}`quoted`, {lit}`%w` when {lit}`identifier`): a
NULL argument is {lit}`NULL` for {lit}`%Q` and {lit}`(NULL)` otherwise, unquoted; {lit}`%q` and
{lit}`%Q` double single quotes, {lit}`%w` double quotes; {lit}`%Q` adds single quotes around the
text; the {lit}`#` flag of {lit}`%q`, and of {lit}`%Q` when the text has a control byte, also
escapes backslashes and control bytes, {lit}`%#Q` then writing {lit}`unistr('...')`. -/
def escapeField (spec : PrintfSpec) (quoted identifier : Bool) (text : Option (List UInt8)) : List UInt8 :=
  let quote : UInt8 := if identifier then 34 else 39
  let (bytes, wrap) := match text with
    | some bytes => (escapedInput spec.bang spec.precision bytes, quoted)
    | none => (escapedInput spec.bang spec.precision ((if quoted then "NULL" else "(NULL)").toUTF8.toList), Bool.false)
  let controls := bytes.any (· ≤ 0x1f)
  let backslashes := spec.alternate && !identifier && (controls || !quoted)
  let body := escapeBody quote backslashes bytes
  let body := if !wrap then body
    else if backslashes then "unistr('".toUTF8.toList ++ body ++ [39, 41] else [39] ++ body ++ [39]
  padField spec.leftJustify (utf8Width spec.bang spec.width body) body

end Belay.Sqlite.Resolved
