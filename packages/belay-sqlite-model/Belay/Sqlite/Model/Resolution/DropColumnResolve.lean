import Belay.Sqlite.Model.Resolution.DropColumnDependents
import Belay.Sqlite.Model.Resolution.Renames

set_option doc.verso true

/-! Name resolution of ALTER TABLE DROP COLUMN. The checks follow {lit}`sqlite3AlterDropColumn` of SQLite 3.51.0:
the table, then the column, then the two schema tests that bracket the edit of the table text. A statement that
passes them is {lit}`Resolved.Statement.dropColumn` with the catalog after the drop ({lit}`Catalog.dropColumn`);
when the drop fails, the statement is a prepare error of SQLite, or the model restriction
{lit}`RestrictionKind.alterDrop` for a drop that the model cannot describe. -/

namespace Belay.Sqlite.Model

/-- Whether one view or trigger of the catalog resolves, in a schema test of SQLite. A table and an index have no
text that the test of this pass reads. -/
def checkLateObject (context : ResolveContext) (catalog : Catalog) (phase : DependentPhase) (position : Nat)
    (object : CatalogObject) : Except RenameFailure Unit :=
  match object.entry with
  | .view view => checkView context catalog object.name phase view
  | .trigger trigger => checkTrigger context catalog position object.name phase trigger
  | .table _ | .index _ => pure ()

/-- Whether one object of the catalog is in order after the drop of the column at {lit}`index` of the table at
{lit}`target`, in the second schema test of SQLite. {lit}`object` is the object of the catalog before the drop, with the positions
of the columns before it; {lit}`stored` is the catalog after the drop, in which a view or a trigger resolves. The table fails
when a definition still names the column ({name}`CatalogTable.dropFailure?`), an index of the table fails when it
reads the column, and a view or a trigger fails when it no longer resolves in {lit}`stored`. A trigger with
{lit}`UPDATE OF` the column is a restriction. -/
def checkDroppedObject (context : ResolveContext) (stored : Catalog) (target index : Nat) (table : CatalogTable)
    (declared tableName : Identifier) (position : Nat) (object : CatalogObject) : Except RenameFailure Unit :=
  match object.entry with
  | .table _ => match (if position = target then table.dropFailure? index declared object.name else none) with
    | some failure => throw failure
    | none => pure ()
  | .index definition =>
    if definition.readsColumn target index then
      if definition.exactNames && !table.quotedRename then
        throw (.prepare (.dependentObject .index object.name .afterDropColumn (.expression (.noSuchColumn declared))))
      else throw (.restricted .alterDrop)
    else pure ()
  | .view _ => checkLateObject context stored .afterDropColumn position object
  | .trigger trigger =>
    if trigger.updatesColumn declared tableName then throw (.restricted .alterDrop)
    else checkLateObject context stored .afterDropColumn position object

/-- The two schema tests of SQLite around the edit: the first finds a view or a trigger that does not resolve
in the catalog as it is, the second finds an object that fails after the drop. The first failure of a test, in
schema order, is the error. -/
def dropColumnTests (context : ResolveContext) (catalog : Catalog) (target index : Nat) (table : CatalogTable)
    (declared tableName : Identifier) : Except RenameFailure Unit := do
  catalog.zipIdx.forM fun (object, position) => checkLateObject context catalog .current position object
  let stored := catalog.dropColumn target index
  catalog.zipIdx.forM fun (object, position) =>
    checkDroppedObject context stored target index table declared tableName position object

/-- The resolution of a drop that passed the checks of SQLite on the table and the column: the failure of a
schema test, the restriction when the model cannot run the drop ({name}`Catalog.droppable`, or a catalog that the
limits do not allow), or the drop with the catalog after it. -/
def finishDropColumn (context : ResolveContext) (catalog : Catalog) (target index : Nat) (table : CatalogTable)
    (declared tableName : Identifier) : StatementResolution :=
  match dropColumnTests context catalog target index table declared tableName with
  | .error failure => failure.resolution catalog
  | .ok () =>
    if catalog.droppable target index && (catalog.dropColumn target index).supported context.profile.limits then
      .ok (.dropColumn target index (catalog.dropColumn target index), catalog.dropColumn target index)
    else restrict [] .alterDrop

/-- Resolve ALTER TABLE DROP COLUMN. Path 0 is the table and path 1 the column. The checks are, in this order: a
schema table is found under every name of it and may not be altered; the table or view exists; the table is no
system table; the target is no view; the table has the column; the column is no part of the primary key and has
no UNIQUE constraint; the table has another column. Then the schema tests run ({name}`finishDropColumn`). -/
def resolveDropColumn (context : ResolveContext) (catalog : Catalog) (tableName column : Identifier)
    (columnToken : String) : StatementResolution :=
  match schemaTableName? tableName with
  | some reported => prepareError catalog (.expression (.tableMayNotBeAltered reported))
  | none => match catalog.alterTarget tableName with
    | none => prepareError catalog (.noSuchTable tableName)
    | some (position, target) =>
      if reservedName target.name then prepareError catalog (.expression (.tableMayNotBeAltered target.name))
      else match target.entry with
        | .view _ => prepareError catalog (.dropColumn (.view target.name))
        | .table table => match columnPosition table.columns column with
          | none => prepareError catalog (.renameNoSuchColumn columnToken)
          | some index =>
            if table.primaryKey.contains index || table.rowidAlias == some index then
              prepareError catalog (.dropColumn (.primaryKey column))
            else if table.inlineUnique.contains index then prepareError catalog (.dropColumn (.unique column))
            else if table.columns.length ≤ 1 then prepareError catalog (.dropColumn (.lastColumn column))
            else finishDropColumn context catalog position index table
              ((table.columns[index]?.map (·.name)).getD column) target.name
        | .index _ | .trigger _ => restrict [] .alterDrop

end Belay.Sqlite.Model
