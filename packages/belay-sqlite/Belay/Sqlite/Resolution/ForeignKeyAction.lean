set_option doc.verso true

/-! The actions of a foreign key as written, which {lit}`PRAGMA foreign_key_list` reports
(ADR 0014, slice 4). The model runs no action: every profile has foreign keys off. -/

namespace Belay.Sqlite.Syntax

/-- The action of {lit}`ON DELETE` or {lit}`ON UPDATE` of a foreign key, which
{lit}`PRAGMA foreign_key_list` reports; {lean}`ForeignKeyAction.noAction` without the clause.
With foreign keys off, SQLite runs no action (ADR 0014, slice 4). -/
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

end Belay.Sqlite.Syntax
