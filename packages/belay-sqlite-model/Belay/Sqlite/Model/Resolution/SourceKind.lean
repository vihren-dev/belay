set_option doc.verso true

/-! The kinds of sources that a scope has. A scope source carries its kind so that a name
trace can say what a name resolved to. -/

namespace Belay.Sqlite.Model

/-- What kind of object a source of a scope is. -/
inductive SourceKind where
  /-- A table of the catalog. -/
  | baseTable
  /-- A table of the fixed initial database of a two-state query, written {lit}`before.t`. -/
  | initialTable
  /-- A stored view of the catalog. -/
  | storedView
  /-- A {lit}`WITH` definition of the statement. -/
  | commonTable
  /-- A subquery in {lit}`FROM`. -/
  | derivedTable
  /-- A table-valued function such as {lit}`json_each`, or a table-valued pragma. -/
  | tableFunction
  /-- The row that an upsert proposed, named {lit}`excluded`. -/
  | proposedRow
  /-- The {lit}`NEW` or {lit}`OLD` row of a trigger. -/
  | triggerRow
  deriving Repr, DecidableEq

end Belay.Sqlite.Model
