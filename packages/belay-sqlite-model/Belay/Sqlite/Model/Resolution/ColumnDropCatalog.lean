import Belay.Sqlite.Model.Resolution.ColumnDropTable
import Belay.Sqlite.Model.Resolution.Catalog

set_option doc.verso true

/-! The catalog after ALTER TABLE DROP COLUMN, and when a drop is one that the model runs on rows
(ADR 0019, D4). {lit}`Catalog.dropColumn` changes only the table and its indexes. A view or a trigger is
syntax that is resolved at each use, so the resolver decides whether it still resolves and stores the
definitions that SQLite writes ({lit}`Resolved.Statement.dropColumn`). {lit}`Catalog.droppable` lists what
the model needs of the other objects, so that no expression keeps a place of the dropped cells. -/

namespace Belay.Sqlite.Model

/-- Whether no CHECK constraint, generated expression or foreign key of the table depends on the column at
{lit}`index`, apart from those of that column, which go with it. A CHECK constraint or generated
expression depends on a column that it reads, and a foreign key on a child column that it names. -/
def CatalogTable.independentOf (index : Nat) (table : CatalogTable) : Bool :=
  (table.columns.eraseIdx index).all (fun column =>
      column.checks.all (!·.condition.readsColumn index) &&
        (column.generated.map (!·.expression.readsColumn index)).getD true &&
        column.foreignKeys.all (!·.columns.contains index)) &&
    table.checks.all (!·.condition.readsColumn index) && table.foreignKeys.all (!·.columns.contains index)

/-- Whether the column at {lit}`index` can leave the table: it is not the only column, it is no part of
the primary key or of a UNIQUE key, and nothing in the table depends on it ({name}`CatalogTable.independentOf`). -/
def CatalogTable.droppable (index : Nat) (table : CatalogTable) : Bool :=
  decide (index < table.columns.length) && decide (2 ≤ table.columns.length) && !table.primaryKey.contains index &&
    table.rowidAlias != some index && !table.uniqueKeys.any (·.contains index) && table.independentOf index

/-- Whether a foreign key of the table names a parent table with the name, compared as SQLite compares names. -/
def CatalogTable.hasParent (name : Identifier) (table : CatalogTable) : Bool :=
  table.allForeignKeys.any (·.table.sameName name)

/-- Whether the object of the catalog keeps the column at {lit}`index` of the table at {lit}`position`
droppable: an index of the table reads no such column, and no table has the table as the parent of a foreign
key. A view and a trigger impose nothing here. -/
def CatalogObject.allowsDrop (name : Identifier) (position index : Nat) (object : CatalogObject) : Bool :=
  match object.entry with
  | .index definition => !definition.readsColumn position index
  | .table other => !other.hasParent name
  | .view _ | .trigger _ => true

/-- Whether the column at {lit}`index` of the table at the catalog position can be dropped by the model: the
table allows it ({name}`CatalogTable.droppable`) and every object of the catalog allows it
({name}`CatalogObject.allowsDrop`). A position that is no table cannot. -/
def Catalog.droppable (catalog : Catalog) (position index : Nat) : Bool :=
  match catalog[position]? with
  | some { name, entry := .table table } => table.droppable index && catalog.all (·.allowsDrop name position index)
  | some { entry := .index _, .. } | some { entry := .view _, .. } | some { entry := .trigger _, .. } => false
  | none => false

/-- The object at a catalog slot after the drop of the column at {lit}`index` of the table at the catalog
position: that table without the column ({lit}`CatalogTable.dropColumnAt`), an index with its positions
changed ({lit}`CatalogIndex.dropColumn`), and every other object as it is. -/
def CatalogObject.dropColumn (position index slot : Nat) (object : CatalogObject) : CatalogObject :=
  match object.entry with
  | .table table => if slot = position then { object with entry := .table (table.dropColumnAt index) } else object
  | .index definition => { object with entry := .index (definition.dropColumn position index) }
  | .view _ | .trigger _ => object

/-- The catalog after the drop of the column at {lit}`index` of the table at the catalog position: that
table without the column and the indexes with their positions changed ({name}`CatalogObject.dropColumn`).
Every other object stays. -/
def Catalog.dropColumn (catalog : Catalog) (position index : Nat) : Catalog :=
  catalog.mapIdx (CatalogObject.dropColumn position index)

end Belay.Sqlite.Model
