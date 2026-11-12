set_option doc.verso true

namespace Belay.Sqlite.Model.Syntax

/-- The action of {lit}`ON DELETE` or {lit}`ON UPDATE` of a foreign key, which
{lit}`PRAGMA foreign_key_list` reports; {lean}`ForeignKeyAction.noAction` without the clause.
With foreign keys off, SQLite runs no action (ADR 0014, slice 4); with them on, a write runs
it for each child row of a parent row that it deletes or whose key it changes (ADR 0018, D4). -/
inductive ForeignKeyAction where
  /-- {lit}`NO ACTION`, also without the clause. -/
  | noAction
  /-- {lit}`RESTRICT`. -/
  | restrict
  /-- {lit}`SET NULL`. -/
  | setNull
  /-- {lit}`SET DEFAULT`. -/
  | setDefault
  /-- {lit}`CASCADE`. -/
  | cascade
  deriving Repr, BEq, DecidableEq

end Belay.Sqlite.Model.Syntax
