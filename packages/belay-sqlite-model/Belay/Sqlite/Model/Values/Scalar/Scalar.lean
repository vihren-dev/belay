import Belay.Sqlite.Model.Values.Scalar.Pattern
import Belay.Sqlite.Model.Values.Scalar.Quote
import Belay.Sqlite.Model.Values.Scalar.Numeric
import Belay.Sqlite.Model.Values.Scalar.Functions.Printf

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- The number of UTF-8 characters of text before its first NUL byte, as SQLite counts them
by lead bytes: each byte that is not a continuation byte ({lit}`0x80` to {lit}`0xBF`) starts a
character. For example, {lean}`utf8Length "hé".toUTF8.toList = 2`. -/
def utf8Length (bytes : List UInt8) : Nat :=
  ((bytesBeforeNul bytes).filter fun byte => byte &&& 0xC0 != 0x80).length

/-- The largest {lit}`zeroblob` that the model computes: 4096 bytes. A larger one is
{name}`FunctionFailure.unmodeled`, so that a proof never builds a long list. -/
def zeroblobLimit : Int := 4096

/-- The longest {lit}`LIKE` or {lit}`GLOB` pattern in bytes ({lit}`SQLITE_LIMIT_LIKE_PATTERN_LENGTH`,
50000 by default); a longer one fails with {lit}`LIKE or GLOB pattern too complex`. -/
def likePatternLimit : Nat := 50000

/-- The result of {lit}`likeFunc` ({lit}`like` and {lit}`glob`): a pattern longer than
{name}`likePatternLimit` fails; with an escape argument, NULL gives NULL, and an escape that is
not one character fails, else the escape replaces {lit}`%` or {lit}`_` when it is one of them;
then NULL when the pattern or the string is NULL, else 1 or 0 by {name}`patternMatches`. -/
def likeResult (dialect : PatternDialect) (pattern string : Value) (escape : Option Value) :
    Except FunctionFailure Value :=
  if likePatternLimit < pattern.textBytes.length then .error .error
  else
    let chosen : Except FunctionFailure (Option (PatternDialect × UInt32)) := match escape with
      | none => .ok (some (dialect, dialect.matchSet))
      | some value => match cText? value with
        | none => .ok none
        | some bytes =>
          if (bytes.filter fun byte => byte &&& 0xC0 != 0x80).length != 1 then .error .error
          else
            let character := (utf8Read bytes).1
            .ok (some ({ dialect with
              matchAll := if character == dialect.matchAll then 0 else dialect.matchAll,
              matchOne := if character == dialect.matchOne then 0 else dialect.matchOne }, character))
    chosen.map fun
      | none => .null
      | some (dialect, character) => match cText? pattern, cText? string with
        | some pattern, some string => .integer (if patternMatches dialect character pattern string then 1 else 0)
        | none, _ | some _, none => .null

/-- The text of the storage class of a value, as {lit}`typeof` gives it. -/
def typeName : Value → List UInt8
  | .integer _ => "integer".toUTF8.toList
  | .real _ => "real".toUTF8.toList
  | .text _ => "text".toUTF8.toList
  | .blob _ => "blob".toUTF8.toList
  | .null => "null".toUTF8.toList

/-- The best of the arguments of scalar {lit}`min` or {lit}`max` ({lit}`minmaxFunc`): NULL when an
argument is NULL; else, from the first argument on, each argument replaces the best one when
{lit}`replaces` holds for the best one and the argument. -/
def bestArgument (replaces : Value → Value → Bool) : Value → List Value → Value
  | best, [] => best
  | best, argument :: rest =>
    if argument.isNull then .null else bestArgument replaces (if replaces best argument then argument else best) rest

end Belay.Sqlite.Model.Resolved
