set_option doc.verso true

/-! The actions of a foreign key as written, which {lit}`PRAGMA foreign_key_list` reports
(ADR 0014, slice 4) and which the writes run when foreign keys are on (ADR 0018, D4). -/

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

/-- The name of an action as {lit}`PRAGMA foreign_key_list` reports it, for example
{lit}`SET NULL`. -/
def ForeignKeyAction.sqlName : ForeignKeyAction → String
  | .noAction => "NO ACTION"
  | .restrict => "RESTRICT"
  | .setNull => "SET NULL"
  | .setDefault => "SET DEFAULT"
  | .cascade => "CASCADE"

end Belay.Sqlite.Model.Syntax
