import Belay.Sqlite.Model.Resolution.Definitions

set_option doc.verso true

/-! Name resolution of ALTER TABLE RENAME TO and RENAME COLUMN. The prepare checks follow the order of
SQLite 3.51.0's {lit}`sqlite3AlterRenameTable` and {lit}`sqlite3AlterRenameColumn`, because SQLite
reports the first error it finds. A statement that passes them is the model restriction
{lit}`RestrictionKind.alterRename` until the schema rewrite is modeled. -/

namespace Belay.Sqlite.Model

/-- The table or view that {lit}`sqlite3LocateTableItem` finds for a name: its catalog position and object.
An index or trigger of that name is not found. -/
def Catalog.alterTarget (catalog : Catalog) (name : Identifier) : Option (Nat × CatalogObject) :=
  match catalog.find name with
  | some (position, object) => match object.entry with
    | .table _ | .view _ => some (position, object)
    | .index _ | .trigger _ => none
  | none => none

/-- Resolve ALTER TABLE RENAME TO. Path 0 is the table and path 1 the new name. The checks are, in this order:
the table or view exists; no table, view or index has the new name; the table is no system table; the new
name is not reserved; the target is no view. -/
def resolveRenameTable (catalog : Catalog) (tableName newName : Identifier) : StatementResolution :=
  match catalog.alterTarget tableName with
  | none => prepareError catalog (.noSuchTable tableName)
  | some (_, target) =>
    if (catalog.find newName).isSome then prepareError catalog (.renameTargetTaken newName)
    else if reservedName target.name then prepareError catalog (.expression (.tableMayNotBeAltered target.name))
    else if reservedName newName then prepareError catalog (.expression (.reservedName newName))
    else match target.entry with
      | .view _ => prepareError catalog (.viewNotAltered target.name)
      | .table _ | .index _ | .trigger _ => restrict [] .alterRename

/-- Resolve ALTER TABLE RENAME COLUMN. Path 0 is the table, path 1 the column and path 2 the new name. The
checks are, in this order: the table or view exists; the table is no system table; the target is no
view; the table has the column. -/
def resolveRenameColumn (catalog : Catalog) (tableName column : Identifier) (columnToken : String) :
    StatementResolution :=
  match catalog.alterTarget tableName with
  | none => prepareError catalog (.noSuchTable tableName)
  | some (_, target) =>
    if reservedName target.name then prepareError catalog (.expression (.tableMayNotBeAltered target.name))
    else match target.entry with
      | .view _ => prepareError catalog (.viewColumnsNotRenamed target.name)
      | .table table => match columnPosition table.columns column with
        | none => prepareError catalog (.renameNoSuchColumn columnToken)
        | some _ => restrict [] .alterRename
      | .index _ | .trigger _ => restrict [] .alterRename

end Belay.Sqlite.Model
