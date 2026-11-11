import Belay.Sqlite.Model.Shared.Values.Declarations

set_option doc.verso true

namespace Belay.Sqlite.Model

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

end Belay.Sqlite.Model
