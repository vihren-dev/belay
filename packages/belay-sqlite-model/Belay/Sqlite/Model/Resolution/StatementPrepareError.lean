import Belay.Sqlite.Model.Resolution.PrepareErrors

set_option doc.verso true

/-! The error that {lit}`sqlite3_prepare_v2` reports for a statement (ADR 0013, D8): one that
checks a statement, names a catalog object, or reports an expression error ({lit}`ExprError`). -/

namespace Belay.Sqlite.Model

/-- The kind of the object that a rename or a drop of a column finds in error ({lit}`PrepareError.dependentObject`). -/
inductive DependentKind where
  /-- A table. -/
  | table
  /-- An index. -/
  | index
  /-- A view. -/
  | view
  /-- A trigger. -/
  | trigger
  deriving Repr, DecidableEq

/-- When a statement finds a stored definition in error ({lit}`PrepareError.dependentObject`): while it
tests the schema before it changes it, or with the definitions after a rename or after the drop of a column. -/
inductive DependentPhase where
  /-- Before the statement changes anything. -/
  | current
  /-- With the definitions that a rename rewrote. -/
  | afterRename
  /-- With the schema after the drop of a column. -/
  | afterDropColumn
  deriving Repr, DecidableEq

/-- The words that SQLite adds to the error of a stored definition for the phase of the statement. -/
def DependentPhase.words : DependentPhase → String
  | .current => ""
  | .afterRename => " after rename"
  | .afterDropColumn => " after drop column"

/-- The errors that {lit}`sqlite3AlterDropColumn` reports before it looks at any other object. The name is the
name of the table or of the column as the message prints it. -/
inductive DropColumnError where
  /-- {lit}`cannot drop column from view "%s"`: the name is the catalog's declared spelling of the view. -/
  | view (name : Identifier)
  /-- {lit}`cannot drop PRIMARY KEY column: "%s"`: the name is the column as the statement writes it. -/
  | primaryKey (column : Identifier)
  /-- {lit}`cannot drop UNIQUE column: "%s"`: the name is the column as the statement writes it. -/
  | unique (column : Identifier)
  /-- {lit}`cannot drop column "%s": no other columns exist`: the name is the column as the statement writes it. -/
  | lastColumn (column : Identifier)
  deriving Repr, DecidableEq

/-- The name that the message of the error prints. -/
def DropColumnError.name : DropColumnError → Identifier
  | .view name | .primaryKey name | .unique name | .lastColumn name => name

/-- An error that {lit}`sqlite3_prepare_v2` reports for a statement in the first
scope. Each constructor names the SQLite message format it corresponds to. This
is a SQLite rule, not a model restriction: SQLite runs the earlier statements and
then stops at this one. -/
inductive PrepareError where
  /-- {lit}`parameters are not allowed in views`, before name checks at CREATE VIEW. -/
  | viewVariables
  /-- {lit}`table %T already exists` ({lit}`sqlite3StartTable`). -/
  | tableExists (name : Identifier)
  /-- {lit}`view %T already exists` ({lit}`sqlite3StartTable`). -/
  | viewExists (name : Identifier)
  /-- {lit}`there is already an index named %s` ({lit}`sqlite3StartTable`). -/
  | indexNameUsed (name : Identifier)
  /-- {lit}`there is already a table named %s` ({lit}`sqlite3CreateIndex`). -/
  | tableNameUsed (name : Identifier)
  /-- {lit}`index %s already exists` ({lit}`sqlite3CreateIndex`). -/
  | indexExists (name : Identifier)
  /-- {lit}`no such table: %s` ({lit}`sqlite3LocateTable`). -/
  | noSuchTable (name : Identifier)
  /-- {lit}`no such view: %s` ({lit}`sqlite3LocateTable` for DROP VIEW). -/
  | noSuchView (name : Identifier)
  /-- {lit}`use DROP TABLE to delete table %s`: DROP VIEW names a physical table.
  The name keeps the catalog's declared spelling. -/
  | useDropTable (name : Identifier)
  /-- {lit}`use DROP VIEW to delete view %s`: DROP TABLE names a view.
  The name keeps the catalog's declared spelling. -/
  | useDropView (name : Identifier)
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
  /-- {lit}`cannot modify %s because it is a view` ({lit}`sqlite3IsReadOnly`): INSERT, UPDATE or
  DELETE of a view that has no INSTEAD OF trigger. The name keeps the catalog's declared spelling. -/
  | viewModify (name : Identifier)
  /-- {lit}`views may not be indexed` ({lit}`sqlite3CreateIndex`). -/
  | viewNotIndexed
  /-- {lit}`Cannot add a column to a view` ({lit}`sqlite3AlterBeginAddColumn`). -/
  | viewAddColumn
  /-- {lit}`there is already another table or index with this name: %s` ({lit}`sqlite3AlterRenameTable`):
  a table, view or index has the new name, also the renamed table itself under another letter case.
  The name is the new name as written. -/
  | renameTargetTaken (name : Identifier)
  /-- {lit}`view %s may not be altered` ({lit}`sqlite3AlterRenameTable`). The name keeps the
  catalog's declared spelling. -/
  | viewNotAltered (name : Identifier)
  /-- {lit}`cannot rename columns of view "%s"` ({lit}`isRealTable` of
  {lit}`sqlite3AlterRenameColumn`). The name keeps the catalog's declared spelling. -/
  | viewColumnsNotRenamed (name : Identifier)
  /-- {lit}`no such column: "%T"` ({lit}`sqlite3AlterRenameColumn`): the table has no column of the
  old name. The text is the token of the statement with its quotes, as SQLite prints it. -/
  | renameNoSuchColumn (token : String)
  /-- {lit}`cannot create BEFORE trigger on view: %S` or {lit}`cannot create AFTER trigger on view: %S`
  ({lit}`sqlite3BeginTrigger`): a view takes only INSTEAD OF triggers. The flag is true for BEFORE.
  The name is the name as written. -/
  | viewTrigger (before : Bool) (name : Identifier)
  /-- A refusal of ALTER TABLE DROP COLUMN ({name}`DropColumnError`). -/
  | dropColumn (error : DropColumnError)
  /-- {lit}`error in view %s: %s`, {lit}`error in view %s after rename: %s`, {lit}`error in view %s after drop column: %s`
  and the same for a table, an index or a trigger: a rename or a drop of a column finds that an object no longer
  resolves, before the change or with the changed definitions ({name}`DependentPhase`). SQLite reports it while the
  statement runs, and the statement changes nothing, as a prepare error does. The error is the one that the
  definition of the object gives. -/
  | dependentObject (kind : DependentKind) (name : Identifier) (phase : DependentPhase) (error : PrepareError)
  /-- An error that names no catalog object ({name}`ExprError`). -/
  | expression (error : ExprError)
  deriving Repr, DecidableEq

/-- Whether SQLite reports the error while the statement runs ({lit}`sqlite3_step`) and not in
{lit}`sqlite3_prepare_v2`: only the error that a rename finds in a dependent object
({name}`PrepareError.dependentObject`), because SQLite rewrites the stored definitions with an SQL function
of the statement. The statement changes nothing in both cases. For example,
{lean}`(PrepareError.noSuchTable (Identifier.ofString "t")).reportedWhileRunning` is false. -/
def PrepareError.reportedWhileRunning : PrepareError → Bool
  | .dependentObject .. => true
  | .viewVariables | .tableExists _ | .viewExists _ | .indexNameUsed _ | .tableNameUsed _
  | .indexExists _ | .noSuchTable _ | .noSuchView _ | .useDropTable _ | .useDropView _
  | .noSuchIndex _ | .tableMayNotBeDropped _ | .noSuchReferencedTable _ | .foreignKeyMismatch ..
  | .noSuchTrigger _ | .triggerExists _ | .viewModify _ | .viewNotIndexed | .viewAddColumn | .viewTrigger ..
  | .renameTargetTaken _ | .viewNotAltered _ | .viewColumnsNotRenamed _ | .renameNoSuchColumn _ | .dropColumn _
  | .expression _ => false

end Belay.Sqlite.Model
