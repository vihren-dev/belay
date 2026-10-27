import Belay.Sqlite.Model.Resolution.RenameDependents
import Belay.Sqlite.Model.Resolution.RenameTables
import Belay.Sqlite.Model.Database

set_option doc.verso true

/-! The catalog after ALTER TABLE RENAME TO and RENAME COLUMN (ADR 0019, D4), in the two passes of SQLite
3.51.0. The first pass rewrites every object in catalog order and fails with the first definition that does not
resolve ({lit}`error in view v: ...`). The second pass resolves every object of the rewritten catalog and fails
with the first that does not ({lit}`error in view v after rename: ...`, and for a table a duplicate column
name). A rename changes no row and no position, so the catalog after it has the objects of the catalog before
it at the same positions. -/

namespace Belay.Sqlite.Model

open Syntax

/-- The position of the table that the rename changes. -/
def RenameTarget.position : RenameTarget → Nat
  | .table position | .column position _ => position

/-- The change of a foreign key that a rename makes: a key whose parent is the renamed table names it with the
new name, or names the renamed column with the new name; {lit}`oldTable` and {lit}`oldColumn` are the names
before the rename. -/
def RenameRequest.foreignKeyChange (request : RenameRequest) (oldTable oldColumn : Identifier) :
    ForeignKey → ForeignKey :=
  match request.target with
  | .table _ => ForeignKey.renameParent oldTable request.new
  | .column _ _ => ForeignKey.renameParentColumn oldTable oldColumn request.new

/-- The renamed table itself: its CHECK texts, the name of the column and its foreign keys. -/
def RenameRequest.renameOwnTable (request : RenameRequest) (oldTable oldColumn : Identifier)
    (table : CatalogTable) : Option CatalogTable :=
  match request.target, request.style with
  | .table _, _ => table.renamedTable oldTable request.new
  | .column _ index, .column quoted => table.renamedColumn oldTable index oldColumn request.new quoted
  | .column _ _, .table => none

/-- One object of the catalog after the rename, in the first pass of SQLite. A table other than the renamed
one changes in the parent names of its foreign keys; an index reads its table by position and does not change.
A table with a double quote in a CHECK text that no name covers is a restriction ({name}`CatalogTable.hasLooseQuote`). -/
def renameObject (context : ResolveContext) (catalog : Catalog) (request : RenameRequest)
    (oldTable oldColumn : Identifier) (position : Nat) (object : CatalogObject) :
    Except RenameFailure CatalogObject :=
  match object.entry with
  | .table table =>
    if table.hasLooseQuote then throw (.restricted .alterRename)
    else if position == request.target.position then
      match request.renameOwnTable oldTable oldColumn table with
      | some renamed => pure { name := match request.target with
          | .table _ => request.new
          | .column _ _ => object.name, entry := .table renamed }
      | none => throw (.restricted .alterRename)
    else pure { object with entry := .table (table.mapForeignKeys (request.foreignKeyChange oldTable oldColumn)) }
  | .index _ => pure object
  | .view view => (fun renamed => { object with entry := .view renamed }) <$>
      renameView context catalog request object.name view
  | .trigger trigger => (fun renamed => { object with entry := .trigger renamed }) <$>
      renameTrigger context catalog request oldColumn position object.name trigger

/-- Whether one object of the catalog after the rename is in order, in the second pass of SQLite: a view and
a trigger resolve, and a table has no two columns of one name. -/
def checkRenamedObject (context : ResolveContext) (catalog : Catalog) (position : Nat) (object : CatalogObject) :
    Except RenameFailure Unit :=
  match object.entry with
  | .table table => match table.duplicateColumn? with
    | some column => throw (.prepare (.dependentObject .table object.name true (.expression (.duplicateColumn column))))
    | none => pure ()
  | .index _ => pure ()
  | .view view => checkView context catalog object.name true view
  | .trigger trigger => checkTrigger context catalog position object.name true trigger

/-- The catalog after the rename of the table or column of the request, or why SQLite or the model stops. The
catalog is also supported under the limits of the profile: a rename to a name that the model does not allow for
a column is a restriction. -/
def renameCatalog (context : ResolveContext) (catalog : Catalog) (request : RenameRequest)
    (oldTable oldColumn : Identifier) : Except RenameFailure Catalog := do
  let renamed ← catalog.zipIdx.mapM fun (object, position) =>
    renameObject context catalog request oldTable oldColumn position object
  renamed.zipIdx.forM fun (object, position) => checkRenamedObject context renamed position object
  if Catalog.supported context.profile.limits renamed then pure renamed else throw (.restricted .alterRename)

end Belay.Sqlite.Model
