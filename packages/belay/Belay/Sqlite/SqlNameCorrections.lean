import Belay.Sqlite.SqlKeywords
import Belay.Sqlite.SqlNameSites
import Lean.Data.EditDistance

set_option doc.verso true

/-! Safe corrections of an unknown name (the editor task, part 2b). The name trace gives, for a
name that no scope has, the names that are legal at that place with their scope sources. This
module ranks them and writes the replacement token. It looks at no scope itself. A correction
changes only the one token of the name. It keeps the quote style that the written token has, and it
gives up when it cannot write the candidate safely in that style. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- The largest case-folded edit distance between a misspelled name and a name that the editor
offers in its place. A name further away is more likely another name than a typo. -/
def correctionDistanceLimit : Nat := 2

/-- The name that a candidate stands for. -/
def candidateName : Candidate → Identifier
  | .column binding => binding.column.name
  | .resultAlias name _ => name
  | .source source => source.name
  | .catalogObject _ name _ => name

/-- The ASCII-folded name as text, or none for bytes that are not UTF-8. -/
def foldedText (name : Identifier) : Option String := String.fromUTF8? (ByteArray.mk name.folded.toArray)

/-- The edit distance of the folded names when it is at least 1 and at most
{name}`correctionDistanceLimit`. A name at distance 0 is the same name for SQLite, so it is no
correction. For example, {lit}`nmae` and {lit}`name` are at distance 2. -/
def nearDistance? (written candidate : Identifier) : Option Nat := do
  let distance ← Lean.EditDistance.levenshtein (← foldedText written) (← foldedText candidate) correctionDistanceLimit
  if 0 < distance && distance ≤ correctionDistanceLimit then some distance else none

/-- The candidates at the smallest edit distance, one name for each folded spelling, in the order
of their folded spelling, so that the order does not depend on the scope. One name is the unique
nearest name; several are a tie, and the editor lists them without choosing. No near name gives the
empty list. -/
def nearestNames (written : Identifier) (candidates : List Candidate) : List Identifier :=
  let distinct := candidates.foldl (fun names candidate =>
    if names.any (·.sameName (candidateName candidate)) then names else names ++ [candidateName candidate]) []
  let scored := distinct.filterMap fun name => (nearDistance? written name).map (name, ·)
  match scored.map (·.2) |>.min? with
  | none => []
  | some best =>
    let nearest := (scored.filter (·.2 == best)).map (·.1)
    nearest.mergeSort fun left right => (foldedText left).getD "" ≤ (foldedText right).getD ""

/-- Whether the text can stay without quotes: ASCII letters, digits and underscores, not starting
with a digit, and no keyword ({name}`sqliteKeywords`). -/
def writesBare (text : String) : Bool :=
  match text.toList with
  | [] => false
  | first :: _ =>
    (first.isAlpha || first == '_') && text.toList.all (fun c => c.isAlphanum || c == '_') &&
      !sqliteKeywords.contains text.toLower

/-- The text of a name in double quotes, with each quote doubled. -/
def doubleQuoted (text : String) : String := "\"" ++ text.replace "\"" "\"\"" ++ "\""

/-- The token that writes the candidate in the style of the written token. A double-quoted or
backtick token stays so; a bracketed token stays so unless the name has a closing bracket; a bare
token stays bare unless the name needs quotes. A token in single quotes, which SQLite reads as a
string, and a name with a NUL byte or invalid UTF-8 give none. For example, the candidate
{lit}`name` replaces {lit}`nmae` as {lit}`name` and replaces {lit}`"nmae"` as {lit}`"name"`. -/
def replacementToken (written : String) (candidate : Identifier) : Option String := do
  let text ← String.fromUTF8? (ByteArray.mk candidate.bytes.toArray)
  if text.contains (Char.ofNat 0) then none else
  match written.front? with
  | some '"' => some (doubleQuoted text)
  | some '`' => some ("`" ++ text.replace "`" "``" ++ "`")
  | some '[' => if text.contains ']' then none else some ("[" ++ text ++ "]")
  | some '\'' => none
  | _ => some (if writesBare text then text else doubleQuoted text)

/-- Whether the editor may correct a name in this role. An alias that the statement declares, and
a comparison, name nothing that a scope could supply. -/
def roleCorrectable : NameRole → Bool
  | .tableReference | .columnReference | .columnTarget | .qualifier => true
  | .aliasDeclaration | .resultAlias | .comparisonSite => false

/-- Whether the editor may correct a name that was missing in this use: an error, or the text
literal of the double-quote fallback. The keywords {lit}`TRUE` and {lit}`FALSE` and the rowid names
are not typos. -/
def useCorrectable : MissingUse → Bool
  | .error | .textLiteral => true
  | .booleanKeyword | .rowidName => false

/-- The unknown name of a place that offers a correction: the occurrence that no scope has, as an
error or as the text literal of the double-quote fallback, with the candidates of its place. -/
def unknownName? (site : NameSite) : Option (Identifier × MissingUse × List Candidate) :=
  site.occurrences.findSome? fun occurrence => match occurrence.result, occurrence.name with
    | .missing use candidates, some name =>
      if roleCorrectable occurrence.role && useCorrectable use then some (name, use, candidates) else none
    | .missing .., none | .found _, _ | .ambiguous _, _ | .source _, _ | .schema _, _
    | .resultColumn _, _ | .declares, _ | .compared .., _ | .unreached _, _ => none

/-- The replacement tokens for the unknown name of a place: one for the unique nearest name, all of
a tie in the order of {name}`nearestNames`. The list is empty when no name is near, and also when
one of the nearest names cannot be written safely ({name}`replacementToken`), because a partial list
would hide an option of the tie. -/
def correctionTokens (written : String) (name : Identifier) (candidates : List Candidate) : List String :=
  (nearestNames name candidates).mapM (replacementToken written) |>.getD []

end Belay.Sqlite
