import Belay.Sqlite.Resolution.Syntax

set_option doc.verso true

/-! The foreign keys of a table (ADR 0014, D2 as amended). Every profile of the model runs
with foreign keys off, as SQLite does by default, so a foreign key changes no write; the
catalog keeps it because {lit}`PRAGMA foreign_key_list` reports it. -/

namespace Belay.Sqlite

/-- One foreign key: the referenced table as written, the positions of its columns in the
table, the referenced columns as written (empty without a column list, which SQLite
reports as NULL), and its actions. -/
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
  deriving Repr, DecidableEq

end Belay.Sqlite
