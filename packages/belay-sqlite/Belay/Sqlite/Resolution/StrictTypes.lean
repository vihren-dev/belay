import Belay.Sqlite.Declarations

set_option doc.verso true

/-! The column types of a {lit}`STRICT` table (ADR 0014, D6): the six types that SQLite
admits, and which storage classes each stores. -/

namespace Belay.Sqlite

/-- The type of a column of a {lit}`STRICT` table. For example, {lit}`a INTEGER` in a
{lit}`STRICT` table has {lean}`StrictType.integer`. -/
inductive StrictType where
  /-- {lit}`INT`. -/
  | int
  /-- {lit}`INTEGER`. -/
  | integer
  /-- {lit}`REAL`. -/
  | real
  /-- {lit}`TEXT`. -/
  | text
  /-- {lit}`BLOB`. -/
  | blob
  /-- {lit}`ANY`: every value, stored as written, without affinity. -/
  | any
  deriving Repr, DecidableEq

/-- The strict type of a declared type as SQLite reports it ({lit}`reportedType`, which
writes the six names in capitals), or none for any other type, which a {lit}`STRICT` table
refuses. -/
def StrictType.ofReported : Option String → Option StrictType
  | some "INT" => some .int
  | some "INTEGER" => some .integer
  | some "REAL" => some .real
  | some "TEXT" => some .text
  | some "BLOB" => some .blob
  | some "ANY" => some .any
  | some _ | none => none

/-- Whether a column of the type stores the value, after the column's affinity applies:
NULL fits every type, {lit}`INT` and {lit}`INTEGER` take integers, {lit}`REAL` integers and
reals, {lit}`TEXT` text, {lit}`BLOB` blobs, and {lit}`ANY` every value (checked natively with
3.51.0). -/
def StrictType.fits : StrictType → Value → Bool
  | _, .null => true
  | .int, .integer _ | .integer, .integer _ => true
  | .real, .integer _ | .real, .real _ => true
  | .text, .text _ | .blob, .blob _ | .any, _ => true
  | .int, .real _ | .int, .text _ | .int, .blob _ | .integer, .real _ | .integer, .text _ | .integer, .blob _
  | .real, .text _ | .real, .blob _ | .text, .integer _ | .text, .real _ | .text, .blob _
  | .blob, .integer _ | .blob, .real _ | .blob, .text _ => false

end Belay.Sqlite
