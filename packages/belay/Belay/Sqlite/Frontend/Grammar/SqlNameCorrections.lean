import Belay.Sqlite.Frontend.Grammar.SqlKeywords
import Lean.Data.EditDistance
import Belay.Sqlite.Model.Shared.Values.Declarations

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model

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

end Belay.Sqlite
