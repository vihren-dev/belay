import Belay.Sqlite.SqlFileLexer

set_option doc.verso true

/-! The markers of an SQL file (ADR 0017, S7): sqlc-style {lit}`-- name: id :one` entries and
goose or dbmate migration directions. A marker is a line comment alone on its line, outside every
statement, so text that only looks like one in a string, a block comment or a trigger body is
not a marker. Positions are UTF-8 byte offsets of the whole file. -/

namespace Belay.Sqlite

/-- The migration direction a marker begins. -/
inductive MigrationDirection where
  /-- The forward migration. -/
  | up
  /-- The reverse migration. -/
  | down
  deriving BEq, Repr, Inhabited

/-- The tool whose marker spelling a direction marker uses. -/
inductive MigrationConvention where
  /-- {lit}`-- +goose Up` and {lit}`-- +goose Down`. -/
  | goose
  /-- {lit}`-- migrate:up` and {lit}`-- migrate:down`. -/
  | dbmate
  deriving BEq, Repr, Inhabited

/-- What a marker comment says. -/
inductive MarkerKind where
  /-- {lit}`-- name: id` with an optional ignored sqlc suffix such as {lit}`:one`. -/
  | named (name : String) (suffix : Option String)
  /-- A comment that starts {lit}`name:` but is not one identifier and an optional suffix. -/
  | malformedName (text : String)
  /-- A standalone migration direction. -/
  | direction (convention : MigrationConvention) (direction : MigrationDirection)
  deriving BEq, Repr, Inhabited

/-- One marker with the documentation lines that follow it. -/
structure SqlMarker where
  /-- The first byte of the marker comment. -/
  start : Nat
  /-- The byte after the marker comment. -/
  stop : Nat
  /-- The meaning of the marker. -/
  kind : MarkerKind
  /-- The ordinary comment lines directly after a named marker, without their {lit}`--`. -/
  documentation : List String := []
  deriving Repr, BEq, Inhabited

/-- The words of a comment's text after {lit}`--`, split at white space. -/
private def words (text : String) : List String :=
  ((text.split fun character => character.isWhitespace).toList.map toString).filter (· != "")

/-- The name marker whose first word starts with {lit}`name:`. A name is one word with at
most one {lit}`:suffix` word after it; anything else is malformed. -/
private def nameMarker (text first : String) (rest : List String) : MarkerKind :=
  match (if first.length > 5 then (first.drop 5).toString :: rest else rest) with
  | [name] => .named name none
  | [name, suffix] =>
    if suffix.startsWith ":" && suffix.length > 1 then .named name (some (suffix.drop 1).toString)
    else .malformedName text
  | _ => .malformedName text

/-- The marker that a comment's text after {lit}`--` writes, if it writes one. Goose accepts
{lit}`+goose Up` and {lit}`+goose Down` in any case and ignores its other directives. Dbmate
accepts {lit}`migrate:up` and {lit}`migrate:down` with any option words after them. -/
def classifyMarker (text : String) : Option MarkerKind :=
  match words text with
  | first :: rest =>
    if first.startsWith "name:" then some (nameMarker text first rest)
    else if first == "+goose" then
      match rest.map String.toLower with
      | ["up"] => some (.direction .goose .up)
      | ["down"] => some (.direction .goose .down)
      | _ => none
    else match first.toLower with
      | "migrate:up" => some (.direction .dbmate .up)
      | "migrate:down" => some (.direction .dbmate .down)
      | _ => none
  | [] => none

/-- The text of a comment between its {lit}`--` and the end. -/
def lineCommentText (bytes : ByteArray) (comment : SqlComment) : String :=
  (String.fromUTF8? (bytes.extract (comment.start + 2) comment.stop)).getD ""

/-- Whether only spaces precede the byte on its line. -/
def aloneOnLine (bytes : ByteArray) (position : Nat) : Bool := Id.run do
  let mut index := position
  while index > 0 && bytes[index - 1]! != 10 do
    index := index - 1
    if !isSqlSpace bytes[index]! then return false
  return true

/-- Whether the gap between two positions is white space with exactly one newline. -/
private def nextLineOnly (bytes : ByteArray) (start stop : Nat) : Bool :=
  let gap := bytes.extract start stop
  gap.toList.all isSqlSpace && (gap.toList.filter (· == 10)).length == 1

/-- The documentation lines after a marker: the ordinary standalone line comments on the
directly following lines, up to a blank line, a statement or another marker. -/
private def documentationAfter (bytes : ByteArray) (comments : Array SqlComment) (marker : SqlComment) : List String × Nat := Id.run do
  let mut lines := []
  let mut stop := marker.stop
  for comment in comments.filter (·.start > marker.stop) do
    if !comment.isLine || !nextLineOnly bytes stop comment.start || !aloneOnLine bytes comment.start
       || (classifyMarker (lineCommentText bytes comment)).isSome then break
    lines := lines ++ [(lineCommentText bytes comment).dropWhile (· == ' ') |>.toString]
    stop := comment.stop
  return (lines, stop)

/-- The markers of the file that lie outside the contents of every statement, in text order.
{lit}`contents` are the half-open byte ranges of the statements without their trailing comments
({name}`statementContentStop`). -/
def sqlMarkers (bytes : ByteArray) (comments : Array SqlComment) (contents : Array (Nat × Nat)) : Array SqlMarker :=
  comments.filterMap fun comment =>
    if !comment.isLine || !aloneOnLine bytes comment.start
       || contents.any (fun (start, stop) => start ≤ comment.start && comment.start < stop) then none
    else (classifyMarker (lineCommentText bytes comment)).map fun kind =>
      match kind with
      | .named .. => { start := comment.start, stop := comment.stop, kind,
                       documentation := (documentationAfter bytes comments comment).1 }
      | .malformedName _ | .direction .. => { start := comment.start, stop := comment.stop, kind }

end Belay.Sqlite
