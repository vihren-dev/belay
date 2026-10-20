import Belay.Sqlite.Comparison

set_option doc.verso true

/-! The scalar functions of ADR 0015 (D2): one constructor for each function that
{lit}`Resolved.Expr.scalar` calls. The JSON and date and time functions keep their own forms
({lit}`JsonFunction`, {lit}`DateFunction`). -/

namespace Belay.Sqlite.Resolved

/-- Which ends {lit}`trim` cuts: {lit}`ltrim` the start, {lit}`rtrim` the end, {lit}`trim` both. -/
inductive TrimSide where
  | leading
  | trailing
  | both
  deriving Repr, DecidableEq

/-- A scalar function of ADR 0015 that resolution gives to {lit}`Resolved.Expr.scalar`. A
function that compares its arguments carries the collation that SQLite chooses for the call:
the collation of the left-most argument that has one, {lit}`BINARY` otherwise. For example,
{lit}`max(a, b)` over two columns without a collation is
{lean}`ScalarFunction.max Collation.binary`. -/
inductive ScalarFunction where
  /-- {lit}`typeof(x)`: the storage class of the value as text. -/
  | typeof
  /-- {lit}`length(x)`: the characters of text before a NUL, the bytes of a BLOB, the bytes
  of the text of a number. -/
  | length
  /-- {lit}`octet_length(x)`: the bytes of the value as text or BLOB. -/
  | octetLength
  /-- {lit}`abs(x)`. -/
  | abs
  /-- {lit}`sign(x)`: -1, 0 or 1 for a number, NULL otherwise. -/
  | sign
  /-- {lit}`zeroblob(n)`: a BLOB of {lit}`n` zero bytes. -/
  | zeroblob
  /-- {lit}`iif` and {lit}`if`: pairs of a condition and a value, and an optional last value. -/
  | iif
  /-- {lit}`nullif(x, y)`: NULL when the arguments are equal under the collation, else {lit}`x`. -/
  | nullif (collation : Collation)
  /-- Scalar {lit}`min(x, y, ...)`: NULL when an argument is NULL, else the least argument
  under the collation, the later one on a tie. -/
  | min (collation : Collation)
  /-- Scalar {lit}`max(x, y, ...)`: NULL when an argument is NULL, else the greatest argument
  under the collation, the earlier one on a tie. -/
  | max (collation : Collation)
  /-- {lit}`like(pattern, x [, escape])`, also the {lit}`LIKE` operator: 1 when {lit}`x` matches
  the pattern without ASCII case, else 0. -/
  | like
  /-- {lit}`glob(pattern, x)`, also the {lit}`GLOB` operator: 1 when {lit}`x` matches the pattern,
  else 0. -/
  | glob
  /-- {lit}`lower(x)`: ASCII letters in lower case. -/
  | lower
  /-- {lit}`upper(x)`: ASCII letters in upper case. -/
  | upper
  /-- {lit}`substr(x, start [, count])` and {lit}`substring`. -/
  | substr
  /-- {lit}`instr(x, y)`: the position of the first {lit}`y` in {lit}`x`. -/
  | instr
  /-- {lit}`replace(x, y, z)`. -/
  | replace
  /-- {lit}`trim`, {lit}`ltrim` and {lit}`rtrim`. -/
  | trim (side : TrimSide)
  /-- {lit}`hex(x)`. -/
  | hex
  /-- {lit}`unhex(x [, ignored])`. -/
  | unhex
  /-- {lit}`quote(x)`. -/
  | quote
  /-- {lit}`unistr_quote(x)`. -/
  | unistrQuote
  /-- {lit}`char(x, ...)`. -/
  | char
  /-- {lit}`unicode(x)`. -/
  | unicode
  /-- {lit}`unistr(x)`: the text with its Unicode escapes replaced. -/
  | unistr
  /-- {lit}`concat(x, ...)`. -/
  | concat
  /-- {lit}`concat_ws(separator, x, ...)`. -/
  | concatWs
  deriving Repr, DecidableEq

/-- Whether the function itself can fail or give a value that the model does not describe:
{lit}`abs` of the smallest integer, a long {lit}`zeroblob`, and {lit}`like` and {lit}`glob` with
a long pattern or an {lit}`ESCAPE` that is not one character, and {lit}`unistr` with an invalid
escape. The other functions fail only through their arguments. -/
def ScalarFunction.canFail : ScalarFunction → Bool
  | .abs | .zeroblob | .like | .glob | .unistr => true
  | .typeof | .length | .octetLength | .sign | .iif | .nullif _ | .min _ | .max _ | .lower | .upper | .substr
  | .instr | .replace | .trim _ | .hex | .unhex | .quote | .unistrQuote | .char | .unicode | .concat
  | .concatWs => false

end Belay.Sqlite.Resolved
