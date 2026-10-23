import Belay.Sqlite.Model.Resolution.PrepareErrors

set_option doc.verso true

/-! The error that {lit}`sqlite3_prepare_v2` reports for a statement (ADR 0013, D8): one that
names a catalog object, or an error of an expression ({lit}`ExprError`). -/

namespace Belay.Sqlite.Model

/-- An error that {lit}`sqlite3_prepare_v2` reports for a statement in the first
scope. Each constructor names the SQLite message format it corresponds to. This
is a SQLite rule, not a model restriction: SQLite runs the earlier statements and
then stops at this one. -/
inductive PrepareError where
  /-- {lit}`table %T already exists` ({lit}`sqlite3StartTable`). -/
  | tableExists (name : Identifier)
  /-- {lit}`there is already an index named %s` ({lit}`sqlite3StartTable`). -/
  | indexNameUsed (name : Identifier)
  /-- {lit}`there is already a table named %s` ({lit}`sqlite3CreateIndex`). -/
  | tableNameUsed (name : Identifier)
  /-- {lit}`index %s already exists` ({lit}`sqlite3CreateIndex`). -/
  | indexExists (name : Identifier)
  /-- {lit}`no such table: %s` ({lit}`sqlite3LocateTable`). -/
  | noSuchTable (name : Identifier)
  /-- {lit}`no such index: %S` ({lit}`sqlite3DropIndex`). -/
  | noSuchIndex (name : Identifier)
  /-- {lit}`table %s may not be dropped` ({lit}`sqlite3DropTable`), for SQLite's schema
  tables: {lit}`sqlite_master` and {lit}`sqlite_temp_master` under any of their names. -/
  | tableMayNotBeDropped (name : Identifier)
  /-- {lit}`no such table: main.%s` ({lit}`sqlite3LocateTable` of the main schema): with foreign
  keys on, a write processes a foreign key whose parent table, named as the key writes it, does
  not exist (ADR 0018, D4); or CREATE TRIGGER names a table that does not exist, or a trigger's
  statement does when a write prepares it (D5). -/
  | noSuchReferencedTable (name : Identifier)
  /-- {lit}`foreign key mismatch - "%w" referencing "%w"` ({lit}`sqlite3FkLocateIndex`): with
  foreign keys on, a write processes a foreign key, of the child table with the first name,
  whose parent, with the second name as the key writes it, has no primary key or unique index
  on the referenced columns (ADR 0018, D4). -/
  | foreignKeyMismatch (child parent : Identifier)
  /-- {lit}`no such trigger: %S` ({lit}`sqlite3DropTrigger`), for DROP TRIGGER without
  {lit}`IF EXISTS` of a name that no trigger has (ADR 0018, D5). -/
  | noSuchTrigger (name : Identifier)
  /-- {lit}`trigger %T already exists` ({lit}`sqlite3BeginTrigger`), for CREATE TRIGGER without
  {lit}`IF NOT EXISTS` (ADR 0018, D5). -/
  | triggerExists (name : Identifier)
  /-- An error that names no catalog object ({name}`ExprError`). -/
  | expression (error : ExprError)
  deriving Repr, DecidableEq

end Belay.Sqlite.Model
