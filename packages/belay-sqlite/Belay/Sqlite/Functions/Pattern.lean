import Belay.Sqlite.ByteText
import Belay.Sqlite.Functions.Utf8

set_option doc.verso true

/-! The pattern matching of {lit}`LIKE` and {lit}`GLOB` (ADR 0015, slice 1), a port of SQLite
3.51.0's {lit}`patternCompare` over C strings. SQLite's function recurses at each wildcard; the
port recurses on a fuel bound ({lit}`patternFuel`), so that the kernel
reduces it. -/

namespace Belay.Sqlite.Resolved

/-- The wildcards of a pattern dialect ({lit}`struct compareInfo`): the character that matches
any text, the one that matches one character (0 when an {lit}`ESCAPE` disables it), the start
of a character class (0 for none) and whether ASCII case is ignored. -/
structure PatternDialect where
  /-- {lit}`%` or {lit}`*`, or 0 when the escape character is this character. -/
  matchAll : UInt32
  /-- {lit}`_` or {lit}`?`, or 0 when the escape character is this character. -/
  matchOne : UInt32
  /-- {lit}`[` for {lit}`GLOB`, 0 for {lit}`LIKE`. -/
  matchSet : UInt32
  /-- Whether ASCII letters compare without case ({lit}`LIKE`). -/
  noCase : Bool
  deriving Repr, DecidableEq

/-- {lit}`GLOB`: {lit}`*`, {lit}`?`, {lit}`[...]`, with case. -/
def globDialect : PatternDialect := { matchAll := 42, matchOne := 63, matchSet := 91, noCase := false }

/-- {lit}`LIKE`: {lit}`%` and {lit}`_`, without ASCII case. -/
def likeDialect : PatternDialect := { matchAll := 37, matchOne := 95, matchSet := 0, noCase := true }

/-- The outcome of a comparison ({lit}`SQLITE_MATCH`, {lit}`SQLITE_NOMATCH`,
{lit}`SQLITE_NOWILDCARDMATCH`): the last stops the search at the wildcards before. -/
inductive PatternResult where
  /-- The string matches the pattern. -/
  | matched
  /-- The string does not match; a wildcard before may try another place. -/
  | noMatch
  /-- The string does not match at any place of the wildcards before. -/
  | noWildcardMatch
  deriving Repr, DecidableEq

/-- An ASCII code point in lower case; other code points stay. -/
def lowerCode (code : UInt32) : UInt32 := if 65 ≤ code && code ≤ 90 then code + 32 else code

/-- An ASCII code point in upper case; other code points stay. -/
def upperCode (code : UInt32) : UInt32 := if 97 ≤ code && code ≤ 122 then code - 32 else code

/-- The members of a character class after its first one: whether the class matches the
character (with {lit}`invert` applied), and the pattern after the {lit}`]`; none when the
pattern ends first. {lit}`a-z` is a range of the member before the {lit}`-`. The fuel bounds
the members. -/
def classMembers (character : UInt32) (invert : Bool) :
    Nat → Bool → UInt32 → UInt32 → List UInt8 → Option (Bool × List UInt8)
  | 0, _, _, _, _ => none
  | fuel + 1, seen, prior, member, pattern =>
    if member == 0 then none
    else if member == 93 then some (seen != invert, pattern)
    else
      let next := pattern.headD 0
      if member == 45 && next != 93 && next != 0 && prior > 0 then
        let (high, after) := utf8Read pattern
        let (following, later) := utf8Read after
        classMembers character invert fuel (seen || (prior ≤ character && character ≤ high)) 0 following later
      else
        let (following, later) := utf8Read pattern
        classMembers character invert fuel (seen || character == member) member following later

/-- Whether a character class matches the character, and the pattern after its {lit}`]`; none
for a class that the pattern does not close. {lit}`^` first negates, a {lit}`]` first is a
member, and {lit}`a-z` is a range. The fuel bounds the members. -/
def classMatches (fuel : Nat) (character : UInt32) (pattern : List UInt8) : Option (Bool × List UInt8) :=
  let (first, rest) := utf8Read pattern
  let (invert, first, rest) := if first == 94 then (true, utf8Read rest |>.1, utf8Read rest |>.2) else (false, first, rest)
  let (seen, first, rest) := if first == 93 then (character == 93, utf8Read rest |>.1, utf8Read rest |>.2)
    else (false, first, rest)
  classMembers character invert fuel seen 0 first rest

mutual
/-- {lit}`patternCompare` of a pattern and a C string, with the escape character
({lit}`matchOther`: the {lit}`ESCAPE` character of {lit}`LIKE`, {lit}`[` of {lit}`GLOB`). The fuel
bounds the steps; {lit}`patternFuel` is enough, and an empty fuel gives no match. -/
def patternCompare (dialect : PatternDialect) (escape : UInt32) : Nat → List UInt8 → List UInt8 → PatternResult
  | 0, _, _ => .noMatch
  | fuel + 1, pattern, string =>
    let (character, rest) := utf8Read pattern
    if character == 0 then (if string.isEmpty then .matched else .noMatch)
    else if character == dialect.matchAll then matchAll dialect escape fuel rest string
    else if character == escape && dialect.matchSet != 0 then
      let (found, after) := utf8Read string
      if found == 0 then .noMatch
      else match classMatches fuel found rest with
        | some (true, later) => patternCompare dialect escape fuel later after
        | some (false, _) | none => .noMatch
    else
      let (character, rest, escaped) :=
        if character == escape then (utf8Read rest |>.1, utf8Read rest |>.2, true) else (character, rest, false)
      if character == 0 then .noMatch
      else
        let (found, after) := utf8Read string
        if character == found then patternCompare dialect escape fuel rest after
        else if dialect.noCase && lowerCode character == lowerCode found && character < 128 && found < 128 then
          patternCompare dialect escape fuel rest after
        else if character == dialect.matchOne && !escaped && found != 0 then patternCompare dialect escape fuel rest after
        else .noMatch

/-- The part of {lit}`patternCompare` after a {lit}`%` or {lit}`*`: skip the wildcards that
follow, consuming one character of the string for each {lit}`_` or {lit}`?`, then search the
string for the next character of the pattern and compare the rest at each place. -/
def matchAll (dialect : PatternDialect) (escape : UInt32) : Nat → List UInt8 → List UInt8 → PatternResult
  | 0, _, _ => .noMatch
  | fuel + 1, pattern, string =>
    let (character, rest) := utf8Read pattern
    if character == dialect.matchAll then matchAll dialect escape fuel rest string
    else if character == dialect.matchOne && dialect.matchOne != 0 then
      let (found, after) := utf8Read string
      if found == 0 then .noWildcardMatch else matchAll dialect escape fuel rest after
    else if character == 0 then .matched
    else if character == escape && dialect.matchSet != 0 then classSearch dialect escape fuel pattern string
    else
      let (character, rest) := if character == escape then utf8Read rest else (character, rest)
      if character == 0 then .noWildcardMatch
      else if character < 128 then byteSearch dialect escape fuel character rest string
      else codeSearch dialect escape fuel character rest string

/-- Search for a class after a wildcard: compare the pattern from its {lit}`[` at each place of
the string. -/
def classSearch (dialect : PatternDialect) (escape : UInt32) : Nat → List UInt8 → List UInt8 → PatternResult
  | 0, _, _ => .noMatch
  | fuel + 1, pattern, string =>
    if string.isEmpty then .noWildcardMatch
    else match patternCompare dialect escape fuel pattern string with
      | .noMatch => classSearch dialect escape fuel pattern (utf8Skip string)
      | .matched => .matched
      | .noWildcardMatch => .noWildcardMatch

/-- Search for an ASCII character after a wildcard, as {lit}`strcspn` does over bytes, in both
cases for {lit}`LIKE`, and compare the rest of the pattern after each place. -/
def byteSearch (dialect : PatternDialect) (escape : UInt32) : Nat → UInt32 → List UInt8 → List UInt8 → PatternResult
  | 0, _, _, _ => .noMatch
  | fuel + 1, character, pattern, string =>
    match string.dropWhile fun byte =>
        !(byte.toUInt32 == character || (dialect.noCase && (byte.toUInt32 == upperCode character ||
          byte.toUInt32 == lowerCode character)))
      with
    | [] => .noWildcardMatch
    | _ :: after => match patternCompare dialect escape fuel pattern after with
      | .noMatch => byteSearch dialect escape fuel character pattern after
      | .matched => .matched
      | .noWildcardMatch => .noWildcardMatch

/-- Search for a character of two or more bytes after a wildcard, character by character, and
compare the rest of the pattern after each place. -/
def codeSearch (dialect : PatternDialect) (escape : UInt32) : Nat → UInt32 → List UInt8 → List UInt8 → PatternResult
  | 0, _, _, _ => .noMatch
  | fuel + 1, character, pattern, string =>
    let (found, after) := utf8Read string
    if found == 0 then .noWildcardMatch
    else if found != character then codeSearch dialect escape fuel character pattern after
    else match patternCompare dialect escape fuel pattern after with
      | .noMatch => codeSearch dialect escape fuel character pattern after
      | .matched => .matched
      | .noWildcardMatch => .noWildcardMatch
end

/-- A fuel that is enough for {name}`patternCompare`: each step consumes a byte of the pattern
or of the string, and each wildcard nests at most once per pattern byte. -/
def patternFuel (pattern string : List UInt8) : Nat := (pattern.length + 2) * (pattern.length + string.length + 2)

/-- Whether the C string matches the pattern ({lit}`patternCompare` is {lit}`SQLITE_MATCH`). -/
def patternMatches (dialect : PatternDialect) (escape : UInt32) (pattern string : List UInt8) : Bool :=
  let pattern := bytesBeforeNul pattern
  let string := bytesBeforeNul string
  patternCompare dialect escape (patternFuel pattern string) pattern string == .matched

end Belay.Sqlite.Resolved
