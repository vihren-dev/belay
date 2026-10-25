import Belay.Sqlite.SqlFileMarkers
import Belay.Sqlite.SqlParameters

set_option doc.verso true

/-! Which statements of an SQL file a form selects (ADR 0017, S7): the whole file, one
migration direction, or the named entries of a module. The functions are pure: they read the
file's bytes and the parser's statement ranges, and either select statements or say what is wrong
and where. The statements keep their positions in the whole file. -/

namespace Belay.Sqlite

/-- What is wrong with a file selection: a message, and the byte range it concerns in the file
when there is one. A problem without a range concerns the form that selects. -/
structure FileProblem where
  /-- The byte range in the file, if the problem is at a place of it. -/
  range : Option (Nat × Nat) := none
  /-- The message that the user reads. -/
  message : String
  deriving Repr, BEq

/-- An SQL file with the ranges of its statements' contents and its markers. -/
structure FileStructure where
  /-- The file's bytes. -/
  bytes : ByteArray
  /-- The half-open byte range of each statement, without its trailing comments. -/
  statements : Array (Nat × Nat)
  /-- The markers outside the statements. -/
  markers : Array SqlMarker

/-- The structure of the file from its statement ranges, which the parser gives. -/
def FileStructure.ofRanges (bytes : ByteArray) (ranges : Array (Nat × Nat)) : FileStructure :=
  let comments := sqlComments bytes
  let statements := ranges.map fun (start, stop) => (start, statementContentStop bytes comments start stop)
  { bytes, statements, markers := sqlMarkers bytes comments statements }

/-- The statements chosen from a file, by index, and the bytes that a replay of them reads. -/
structure FileSelection where
  /-- The indexes of the chosen statements, in file order. -/
  statements : Array Nat
  /-- The first byte of the text that contains exactly these statements. -/
  replayStart : Nat
  /-- The byte after that text. -/
  replayStop : Nat

/-- The indexes of the statements that start in the byte range. -/
private def statementsIn (structure_ : FileStructure) (start stop : Nat) : Array Nat :=
  (Array.range structure_.statements.size).filter fun index =>
    let begin_ := structure_.statements[index]!.1
    start ≤ begin_ && begin_ < stop

/-- The direction markers with their convention and direction, in file order. -/
private def directionMarkers (structure_ : FileStructure) :
    Array (SqlMarker × MigrationConvention × MigrationDirection) :=
  structure_.markers.filterMap fun marker => match marker.kind with
    | .direction convention direction => some (marker, convention, direction)
    | _ => none

/-- The whole file as one script. A file with migration directions is refused, because running
both directions together would undo the migration it applies. -/
def selectWholeFile (structure_ : FileStructure) : Except FileProblem FileSelection := do
  if let some (marker, _, _) := (directionMarkers structure_)[0]? then
    throw { range := some (marker.start, marker.stop), message :=
      "the file has migration direction markers; select one direction with (section := \"up\") or (section := \"down\")" }
  return { statements := Array.range structure_.statements.size, replayStart := 0, replayStop := structure_.bytes.size }

/-- The direction named by the section text of a form. -/
def parseSection : String → Except FileProblem MigrationDirection
  | "up" => .ok .up
  | "down" => .ok .down
  | other => .error { message := s!"unknown section \"{other}\"; use \"up\" or \"down\"" }

/-- The statements of one migration direction. Each direction occurs at most once, the two
conventions are not mixed, and nothing but comments and spaces comes before the first
direction. -/
def selectSection (structure_ : FileStructure) (wanted : MigrationDirection) : Except FileProblem FileSelection := do
  let directions := directionMarkers structure_
  let some (first, convention, _) := directions[0]?
    | throw { message := "the file has no migration direction markers; remove the section, or mark the directions with -- +goose Up/Down or -- migrate:up/down" }
  for (marker, other, _) in directions do
    if other != convention then
      throw { range := some (marker.start, marker.stop), message := "the file mixes goose and dbmate direction markers; use one convention" }
  for index in [1:directions.size] do
    let (marker, _, direction) := directions[index]!
    if directions.extract 0 index |>.any (·.2.2 == direction) then
      throw { range := some (marker.start, marker.stop), message := "this migration direction occurs more than once" }
  if let some (start, stop) := structure_.statements.find? (·.1 < first.start) then
    throw { range := some (start, stop), message := "SQL before the first migration direction marker; only comments may come before it" }
  let some position := directions.findIdx? (·.2.2 == wanted)
    | throw { message := "the file has no marker for the requested migration direction" }
  let (marker, _, _) := directions[position]!
  let stop := (directions[position + 1]?.map (·.1.start)).getD structure_.bytes.size
  return { statements := statementsIn structure_ marker.stop stop, replayStart := marker.stop, replayStop := stop }

/-- One named statement of a module: its identifier, the documentation lines after its marker,
the marker's range, and the index of its one statement. -/
structure NamedEntry where
  /-- The Lean identifier that names the definition. -/
  name : String
  /-- The marker with its documentation. -/
  marker : SqlMarker
  /-- The index of the entry's statement. -/
  statement : Nat

/-- The named entries of a file, each marker owning exactly one statement. Direction markers,
duplicate or malformed names, SQL without a name, and empty or multi-statement entries are
errors. A file without markers or statements gives no entries. -/
def selectNamed (structure_ : FileStructure) : Except FileProblem (Array NamedEntry) := do
  if let some (marker, _, _) := (directionMarkers structure_)[0]? then
    throw { range := some (marker.start, marker.stop), message :=
      "a named SQL module cannot have migration direction markers; use sql_file with (section := ...)" }
  let named := structure_.markers.filterMap fun marker => match marker.kind with
    | .named name _ => some (marker, name)
    | .malformedName text => some (marker, s!"?{text}")
    | _ => none
  if let some (start, stop) := structure_.statements.find? (·.1 < (named[0]?.map (·.1.start)).getD structure_.bytes.size) then
    throw { range := some (start, stop), message := "SQL without a name; put a -- name: marker before it" }
  let mut entries := #[]
  for index in [0:named.size] do
    let (marker, name) := named[index]!
    if let .malformedName text := marker.kind then
      throw { range := some (marker.start, marker.stop), message :=
        s!"the name marker \"{text.trimAscii}\" must be -- name: identifier, with an optional :suffix" }
    unless isLeanIdentifier name do
      throw { range := some (marker.start, marker.stop), message := s!"the name {name} is not one Lean identifier" }
    if entries.any (·.name == name) then
      throw { range := some (marker.start, marker.stop), message := s!"the name {name} is used by more than one entry" }
    let owned := statementsIn structure_ marker.stop ((named[index + 1]?.map (·.1.start)).getD structure_.bytes.size)
    match owned.toList with
    | [statement] => entries := entries.push { name, marker, statement }
    | [] => throw { range := some (marker.start, marker.stop), message := s!"the entry {name} has no SQL statement" }
    | _ :: (second : Nat) :: _ =>
      let (start, stop) := structure_.statements[second]!
      throw { range := some (start, stop), message := s!"the entry {name} has more than one SQL statement; give each statement its own name" }
  return entries

end Belay.Sqlite
