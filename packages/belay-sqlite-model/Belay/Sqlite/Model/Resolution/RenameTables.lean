import Belay.Sqlite.Model.Resolution.RenameChecks
import Belay.Sqlite.Model.Resolution.CatalogObjects

set_option doc.verso true

/-! The tables of the catalog after a rename (ADR 0019, D4). A table holds resolved forms: its CHECK
conditions, generated expressions and keys read columns by position, so a rename leaves them as they are.
What a rename changes in a table is its name or the name of one of its columns, the text and label of its
CHECK constraints, and the names that its foreign keys use for their parent, which are names as written. -/

namespace Belay.Sqlite.Model

open Syntax

/-- The foreign key after the table named {lit}`old` is renamed: a key whose parent is that table names the
new name. -/
def ForeignKey.renameParent (old new : Identifier) (key : ForeignKey) : ForeignKey :=
  if key.table.sameName old then { key with table := new } else key

/-- The foreign key after the column {lit}`column` of the table {lit}`parent` is renamed: a key whose parent is
that table and that names the column in its list of referenced columns names the new name. -/
def ForeignKey.renameParentColumn (parent column new : Identifier) (key : ForeignKey) : ForeignKey :=
  if key.table.sameName parent then
    { key with referenced := key.referenced.map fun name => if name.sameName column then new else name }
  else key

/-- The table with a change applied to every foreign key: those of the columns, then those of the table. -/
def CatalogTable.mapForeignKeys (change : ForeignKey → ForeignKey) (table : CatalogTable) : CatalogTable :=
  { table with
    columns := table.columns.map fun column => { column with foreignKeys := column.foreignKeys.map change },
    foreignKeys := table.foreignKeys.map change }

/-- The table with every CHECK constraint renamed for the target: the constraints of the columns, then those of
the table. None when the tokens of a text do not lie in it. -/
def CatalogTable.renameChecks (target : LabelTarget) (style : RenameStyle) (new : Identifier)
    (table : CatalogTable) : Option CatalogTable := do
  let columns ← table.columns.mapM fun column => do
    let checks ← column.checks.mapM (·.rename target style new)
    pure { column with checks }
  let checks ← table.checks.mapM (·.rename target style new)
  pure { table with columns, checks }

/-- Whether a CHECK constraint of the table has a double quote that no name covers
({name}`CheckText.hasLooseQuote`). -/
def CatalogTable.hasLooseQuote (table : CatalogTable) : Bool :=
  (table.checks ++ table.columns.flatMap (·.checks)).any fun check =>
    (check.source.map CheckText.hasLooseQuote).getD false

/-- The table with the name of the column at the index replaced. -/
def CatalogTable.renameColumnAt (index : Nat) (new : Identifier) (table : CatalogTable) : CatalogTable :=
  { table with columns := table.columns.modify index fun column => { column with name := new } }

/-- The renamed table itself after a table rename: the text of its CHECK constraints names the table with
the new name. Its foreign keys that name itself change like those of every table. -/
def CatalogTable.renamedTable (old new : Identifier) (table : CatalogTable) : Option CatalogTable :=
  (table.renameChecks .table .table new).map (·.mapForeignKeys (ForeignKey.renameParent old new))

/-- The renamed table after a column rename: the column has its new name, the text of its CHECK constraints
names the column with it, and its foreign keys that reference the column of the table itself change like
those of every table. -/
def CatalogTable.renamedColumn (tableName : Identifier) (index : Nat) (old new : Identifier) (quoted : Bool)
    (table : CatalogTable) : Option CatalogTable :=
  ((table.renameChecks (.column index) (.column quoted) new).map (·.renameColumnAt index new)).map
    (·.mapForeignKeys (ForeignKey.renameParentColumn tableName old new))

/-- The names of the columns of the table, two of which are one name for SQLite when their folds are equal:
the first column whose name an earlier column already has, which SQLite reports as a duplicate column. -/
def CatalogTable.duplicateColumn? (table : CatalogTable) : Option Identifier :=
  (table.columns.zipIdx.find? fun (column, index) =>
    (table.columns.take index).any (·.name.sameName column.name)).map (·.1.name)

end Belay.Sqlite.Model
