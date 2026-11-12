import Belay.Sqlite.Model.Shared.Resolved.ForeignKeyAction

set_option doc.verso true

/-! The actions of a foreign key as written, which {lit}`PRAGMA foreign_key_list` reports
(ADR 0014, slice 4) and which the writes run when foreign keys are on (ADR 0018, D4). -/

namespace Belay.Sqlite.Model.Syntax

/-- The name of an action as {lit}`PRAGMA foreign_key_list` reports it, for example
{lit}`SET NULL`. -/
def ForeignKeyAction.sqlName : ForeignKeyAction → String
  | .noAction => "NO ACTION"
  | .restrict => "RESTRICT"
  | .setNull => "SET NULL"
  | .setDefault => "SET DEFAULT"
  | .cascade => "CASCADE"

end Belay.Sqlite.Model.Syntax
