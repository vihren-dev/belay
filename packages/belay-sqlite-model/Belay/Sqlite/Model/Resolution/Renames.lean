import Belay.Sqlite.Model.CheckFailures
import Belay.Sqlite.Model.Resolution.Definitions
import Belay.Sqlite.Model.Resolution.Drops
import Belay.Sqlite.Model.Resolution.RenameCatalog

set_option doc.verso true

/-! Name resolution of ALTER TABLE RENAME TO and RENAME COLUMN. The prepare checks follow the order of
SQLite 3.51.0's {lit}`sqlite3AlterRenameTable` and {lit}`sqlite3AlterRenameColumn`, because SQLite
reports the first error it finds. A statement that passes them rewrites the catalog
({lit}`renameCatalog`): its resolved form is {lit}`Resolved.Statement.rewrite` with the new catalog. When the
rewrite fails, the statement is a prepare error of SQLite, or the model restriction
{lit}`RestrictionKind.alterRename` for a rewrite that the model cannot describe. -/

namespace Belay.Sqlite.Model

/-- The table or view that {lit}`sqlite3LocateTableItem` finds for a name: its catalog position and object.
An index or trigger of that name is not found. -/
def Catalog.alterTarget (catalog : Catalog) (name : Identifier) : Option (Nat × CatalogObject) :=
  match catalog.find name with
  | some (position, object) => match object.entry with
    | .table _ | .view _ => some (position, object)
    | .index _ | .trigger _ => none
  | none => none

/-- Whether a table of the catalog has an index of a UNIQUE or PRIMARY KEY constraint with the name
({name}`autoindexName`), compared with ASCII case ignored. SQLite keeps these indexes in the name space
of tables and indexes, also the one of a {lit}`WITHOUT ROWID` primary key, so a table cannot take their names. -/
def Catalog.constraintIndexTaken (catalog : Catalog) (name : Identifier) : Bool :=
  catalog.any fun object => match object.entry with
    | .table table => (List.range table.constraintKeys.length).any fun number =>
      (autoindexName object.name (number + 1)).sameName name
    | .view _ | .index _ | .trigger _ => false

/-- Whether SQLite finds a table or index with the name in the main database: a table, view or index of the
catalog, the schema table under {lit}`sqlite_master` or {lit}`sqlite_schema`, or the index of a constraint.
The schema table of the temp database is found under its names only when SQLite searches that database. -/
def Catalog.nameTaken (catalog : Catalog) (name : Identifier) : Bool :=
  (catalog.find name).isSome || name.sameName (name! "sqlite_master") || name.sameName (name! "sqlite_schema") ||
    catalog.constraintIndexTaken name

/-- Whether the name is taken in the database of the schema table that {name}`schemaTableName?` reports.
The model has no temp objects, so the temp database holds only its schema table, which SQLite finds under the
names of both schema tables; the main database holds the objects of the catalog. -/
def schemaNameTaken (catalog : Catalog) (reported newName : Identifier) : Bool :=
  if reported.sameName (name! "sqlite_temp_master") then (schemaTableName? newName).isSome
  else catalog.nameTaken newName

/-- The resolution of a rename that passed the checks of SQLite: the new catalog of {name}`renameCatalog` as a
rewrite, or the failure of the rewrite with the catalog unchanged. -/
def finishRename (context : ResolveContext) (catalog : Catalog) (request : RenameRequest)
    (oldTable oldColumn : Identifier) : StatementResolution :=
  match renameCatalog context catalog request oldTable oldColumn with
  | .ok renamed => .ok (.rewrite renamed, renamed)
  | .error failure => failure.resolution catalog

/-- Resolve ALTER TABLE RENAME TO. Path 0 is the table and path 1 the new name. The checks are, in this order:
the table or view exists, where a schema table is found under every name of it; no table, view or index
has the new name; the table is no system table; the new name is not reserved; the target is no view. Then the
catalog is rewritten ({name}`finishRename`). -/
def resolveRenameTable (context : ResolveContext) (catalog : Catalog) (tableName newName : Identifier) :
    StatementResolution :=
  match schemaTableName? tableName with
  | some reported =>
    if schemaNameTaken catalog reported newName then prepareError catalog (.renameTargetTaken newName)
    else prepareError catalog (.expression (.tableMayNotBeAltered reported))
  | none => match catalog.alterTarget tableName with
    | none => prepareError catalog (.noSuchTable tableName)
    | some (position, target) =>
      if catalog.nameTaken newName then prepareError catalog (.renameTargetTaken newName)
      else if reservedName target.name then prepareError catalog (.expression (.tableMayNotBeAltered target.name))
      else if reservedName newName then prepareError catalog (.expression (.reservedName newName))
      else match target.entry with
        | .view _ => prepareError catalog (.viewNotAltered target.name)
        | .table _ => finishRename context catalog { target := .table position, new := newName, style := .table }
            target.name target.name
        | .index _ | .trigger _ => restrict [] .alterRename

/-- Resolve ALTER TABLE RENAME COLUMN. Path 0 is the table, path 1 the column and path 2 the new name. The
checks are, in this order: the table or view exists, where a schema table is found under every name of it;
the table is no system table; the target is no view; the table has the column. Then the catalog is rewritten
({name}`finishRename`); {lit}`quoted` tells whether the new name was written with a quote. -/
def resolveRenameColumn (context : ResolveContext) (catalog : Catalog) (tableName column newName : Identifier)
    (columnToken : String) (quoted : Bool) : StatementResolution :=
  match schemaTableName? tableName with
  | some reported => prepareError catalog (.expression (.tableMayNotBeAltered reported))
  | none => match catalog.alterTarget tableName with
    | none => prepareError catalog (.noSuchTable tableName)
    | some (position, target) =>
      if reservedName target.name then prepareError catalog (.expression (.tableMayNotBeAltered target.name))
      else match target.entry with
        | .view _ => prepareError catalog (.viewColumnsNotRenamed target.name)
        | .table table => match columnPosition table.columns column with
          | none => prepareError catalog (.renameNoSuchColumn columnToken)
          | some index => finishRename context catalog
              { target := .column position index, new := newName, style := .column quoted } target.name
              ((table.columns[index]?.map (·.name)).getD column)
        | .index _ | .trigger _ => restrict [] .alterRename

/-- Resolve ALTER TABLE DROP COLUMN. Path 0 is the table and path 1 the column. -/
def resolveDropColumn (_context : ResolveContext) (_catalog : Catalog) (_tableName _column : Identifier)
    (_columnToken : String) : StatementResolution :=
  restrict [] .alterDrop

/-- For every resolution input, {name}`resolveDropColumn` is no success while the statement is only a
restriction. Proof sketch: the resolver is {name}`restrict`, which is an error. -/
theorem resolveDropColumn_no_success (context : ResolveContext) (catalog : Catalog)
    (tableName column : Identifier) (columnToken : String) (result : Resolved.Statement × Catalog) :
    resolveDropColumn context catalog tableName column columnToken ≠ .ok result := by
  simp [resolveDropColumn, restrict]

end Belay.Sqlite.Model
