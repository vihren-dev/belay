import Belay.Sqlite.Model.Resolution.Syntax

set_option doc.verso true

/-! The foreign keys of a table (ADR 0014, D2 as amended). The catalog keeps them because
{lit}`PRAGMA foreign_key_list` reports them, and the writes check them when foreign keys are on
(ADR 0018, D4). -/

namespace Belay.Sqlite.Model

/-- One foreign key: the referenced table as written, the positions of its columns in the
table, the referenced columns as written (empty without a column list, which SQLite
reports as NULL), its actions, and whether it is deferred. -/
structure ForeignKey where
  /-- The referenced table, as written. -/
  table : Identifier
  /-- The positions of the columns of the key in its table, in written order. -/
  columns : List Nat
  /-- The referenced columns as written; empty without a column list. -/
  referenced : List Identifier
  /-- The {lit}`ON DELETE` action. -/
  onDelete : Syntax.ForeignKeyAction
  /-- The {lit}`ON UPDATE` action. -/
  onUpdate : Syntax.ForeignKeyAction
  /-- Whether the key is {lit}`DEFERRABLE INITIALLY DEFERRED`, which SQLite checks at
  {lit}`COMMIT`; {lean}`false` for an immediate key. -/
  deferred : Bool := false
  deriving Repr, DecidableEq

end Belay.Sqlite.Model
