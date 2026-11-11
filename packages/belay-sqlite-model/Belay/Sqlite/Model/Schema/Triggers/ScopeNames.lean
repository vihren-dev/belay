import Belay.Sqlite.Model.Queries.Preparation.Scope

set_option doc.verso true

/-! The resolution of names over a scope (ADR 0012, amendment 2, "Names"; ADR 0018, D1 and
D5): unqualified names from the query's own sources outward, qualified names over the sources of
the qualifier, the rowid names, {lit}`source.*`, and the {lit}`NEW` and {lit}`OLD` rows of a
trigger, which only a qualified name sees. -/

namespace Belay.Sqlite.Model

/-- The {lit}`NEW` and {lit}`OLD` rows of a trigger as the statements of its body see them (ADR
0018, D5): the columns of the trigger's table, and whether the event has {lit}`NEW` (INSERT and
UPDATE) and {lit}`OLD` (UPDATE and DELETE). -/
structure TriggerRow where
  /-- The columns of the trigger's table. -/
  columns : List CatalogColumn
  /-- Whether the event has {lit}`NEW`. -/
  new : Bool
  /-- Whether the event has {lit}`OLD`. -/
  old : Bool

/-- The sources of the rows that the event has, at the offset: {lit}`NEW`'s cells first when
the event has it, then {lit}`OLD`'s, each with a rowid, so that {lit}`new.rowid` is the
restriction of a rowid name. -/
def TriggerRow.scope (row : TriggerRow) (offset : Nat) : Scope :=
  let new : ScopeSource := { name := name! "new", columns := row.columns, offset, trigger := true, role := .triggerRow }
  let old : ScopeSource :=
    { new with name := name! "old", offset := offset + if row.new then row.columns.length else 0 }
  (if row.new then [new] else []) ++ (if row.old then [old] else [])

/-- The number of cells of the rows: one for each column in each row that the event has. -/
def TriggerRow.width (row : TriggerRow) : Nat :=
  ((if row.new then 1 else 0) + (if row.old then 1 else 0)) * row.columns.length

end Belay.Sqlite.Model
