import Belay.Sqlite.SqlFileSource
import Belay.Sqlite.SqlFileLayout
import Belay.Sqlite.SqlDiagnostics

set_option doc.verso true

namespace Belay.Sqlite
open Lean

/-- The SQL path with the one-based line and character column of a UTF-8 byte offset of the file.
The parser counts bytes, while Lean's file map counts Unicode characters; CRLF line ends count
as one line end. -/
def SqlFileSource.location (source : SqlFileSource) (offset : Nat) : String :=
  let position := (FileMap.ofString source.text).toPosition ⟨min offset source.text.utf8ByteSize⟩
  s!"{source.path}:{position.line}:{position.column + 1}"

/-- Render an external SQL diagnostic with its original location. The Lean form remains the
diagnostic's own location, while this message identifies the SQL file and entry. -/
def SqlFileSource.diagnostic (source : SqlFileSource) (diagnostic : Diagnostic)
    (entry : Option String := none) : String :=
  let statement := entry.map (fun name => s!"in statement `{name}`: ") |>.getD ""
  s!"{source.location diagnostic.start}: {statement}{diagnostic.message}"

/-- Render a selection problem: at its range in the file when it has one, else for the whole
file. The Lean form stays the diagnostic's location, as for {name}`SqlFileSource.diagnostic`. -/
def SqlFileSource.problem (source : SqlFileSource) (problem : FileProblem) (entry : Option String := none) : String :=
  match problem.range with
  | some (start, stop) => source.diagnostic { start, stop, message := problem.message } entry
  | none => s!"{source.path}: {problem.message}"

/-- Whether the byte can be part of a dotted SQL word. -/
private def isWordByte (byte : UInt8) : Bool :=
  (48 ≤ byte && byte ≤ 57) || (65 ≤ byte && byte ≤ 90) || (97 ≤ byte && byte ≤ 122) || byte == 95 || byte == 46

/-- An explanation for a parser refusal at a byte offset when the text there is syntax of another
tool: a sqlite3 shell dot command such as {lit}`.mode csv` at the start of a line, or a sqlc macro
such as {lit}`sqlc.arg(id)`. Both are refused by SQLite's grammar and need conversion to SQL.
Quoted text and comments never refuse, so they are never explained this way. -/
def toolSyntaxHint (bytes : ByteArray) (offset : Nat) : Option String := Id.run do
  let mut lineStart := offset
  while lineStart > 0 && bytes[lineStart - 1]! != 10 do lineStart := lineStart - 1
  while lineStart < offset && (bytes[lineStart]! == 32 || bytes[lineStart]! == 9 || bytes[lineStart]! == 13) do
    lineStart := lineStart + 1
  if lineStart == offset && bytes[offset]? == some 46 && (bytes[offset + 1]?.any fun byte =>
      (65 ≤ byte && byte ≤ 90) || (97 ≤ byte && byte ≤ 122)) then
    return some "this is a sqlite3 shell dot command, not SQL; remove it from the file or run it outside the file"
  let mut wordStart := offset
  while wordStart > 0 && isWordByte bytes[wordStart - 1]! do wordStart := wordStart - 1
  let word := String.fromUTF8? (bytes.extract wordStart offset) |>.getD ""
  if word.startsWith "sqlc." then
    return some s!"{word} is sqlc macro syntax, not SQLite; convert it to a parameter such as :name or @name before use"
  return none

end Belay.Sqlite
