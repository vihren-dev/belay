import Belay.Sqlite.Model.Resolution.CatalogObjects

set_option doc.verso true

/-! The functions over the catalog that resolution and execution share: column affinities,
unique keys, the changes of CREATE TABLE, CREATE INDEX, CREATE TRIGGER and ADD COLUMN, and the
names of the catalog's objects. The object types are in {lit}`CatalogObjects`. -/

namespace Belay.Sqlite.Model

/-- The affinity of a column from its declared type; {lit}`BLOB` for a {lit}`STRICT` table's {lit}`ANY`. -/
def CatalogColumn.affinity (column : CatalogColumn) : Affinity :=
  if column.strictType == some .any then .blob else affinityOf column.declaredType

/-- The key of the column positions of a table with the columns, without filter, each under
its column's collation: a primary key or UNIQUE constraint. -/
def UniqueKey.ofColumns (columns : List CatalogColumn) (positions : List Nat) : UniqueKey :=
  { terms := positions.map fun position =>
      { term := .column position, collation := (columns[position]?.map (·.collation)).getD .binary } }

/-- Each unique key of the table at a catalog position, in this order: the primary key
when there is one, the UNIQUE constraints, and the unique indexes on the table in
catalog order. SQLite keeps each of them as an index, and a write that makes two rows
equal on one of them fails. -/
def Catalog.uniqueKeys (catalog : Catalog) (position : Nat) (table : CatalogTable) : List UniqueKey :=
  ((if table.primaryKey.isEmpty then [] else [table.primaryKey]) ++ table.uniqueKeys).map
      (UniqueKey.ofColumns table.columns) ++
    catalog.filterMap fun object => match object.entry with
      | .index index => if index.table == position && index.unique then some index.uniqueKey else none
      | .table _ | .view _ | .trigger _ => none

/-- Add the table with the name at the end of the catalog, at position {lean}`catalog.length`, as
CREATE TABLE does. The resolver and the execution of CREATE TABLE both use it, so they agree. -/
def Catalog.createTable (catalog : Catalog) (name : Identifier) (table : CatalogTable) : Catalog :=
  catalog ++ [{ name, entry := .table table }]

/-- Append an unresolved view. This primitive stores names, so dropping an earlier
catalog object cannot leave stale positions in the view's definition. -/
def Catalog.createView (catalog : Catalog) (name : Identifier) (view : CatalogView) : Catalog :=
  catalog ++ [{ name, entry := .view view }]

/-- Find a named view and its catalog position. A table or index of that name gives
{lean}`(none : Option (Nat × CatalogView))`; trigger names are separate. -/
def Catalog.findView (catalog : Catalog) (name : Identifier) : Option (Nat × CatalogView) :=
  match catalog.find name with
  | some (position, { entry := .view view, .. }) => some (position, view)
  | some (_, { entry := .table _, .. }) | some (_, { entry := .index _, .. })
  | some (_, { entry := .trigger _, .. }) | none => none

/-- A name that finds a physical table cannot also find a view. Proof sketch:
both lookups read the same first object in their shared namespace. -/
theorem Catalog.findView_none_of_table {catalog : Catalog} {name : Identifier}
    {position : Nat} {table : CatalogTable} (found : catalog.findTable name = some (position, table)) :
    catalog.findView name = none := by
  unfold Catalog.findTable at found
  unfold Catalog.findView
  split at found <;> simp_all

/-- Add the index with the name at the end of the catalog, as CREATE INDEX does. -/
def Catalog.createIndex (catalog : Catalog) (name : Identifier) (index : CatalogIndex) : Catalog :=
  catalog ++ [{ name, entry := .index index }]

/-- Add the trigger with the name at the end of the catalog, as CREATE TRIGGER does
(ADR 0018, D5). -/
def Catalog.createTrigger (catalog : Catalog) (name : Identifier) (trigger : CatalogTrigger) : Catalog :=
  catalog ++ [{ name, entry := .trigger trigger }]

/-- The first trigger of the catalog whose folded name equals the folded given name, with its
position. -/
def Catalog.findTrigger (catalog : Catalog) (name : Identifier) : Option (Nat × CatalogTrigger) :=
  catalog.zipIdx.findSome? fun (object, position) => match object.entry with
    | .trigger trigger => if object.name.sameName name then some (position, trigger) else none
    | .table _ | .view _ | .index _ => none

/-- Append the column to the table at the position, keeping the table's name and every
other object, as ALTER TABLE ADD COLUMN does. A non-table or absent position is unchanged. The resolver and the execution of ADD COLUMN both use it. -/
def Catalog.addColumn (catalog : Catalog) (position : Nat) (column : CatalogColumn) : Catalog :=
  match catalog[position]? with
  | some { name, entry := .table table } =>
    catalog.set position { name, entry := .table { table with columns := table.columns ++ [column] } }
  | some { entry := .index _, .. } | some { entry := .view _, .. } | some { entry := .trigger _, .. } => catalog
  | none => catalog

/-- The folded names of the tables, views and indexes of the catalog, in catalog order; triggers have a
namespace of their own. -/
def Catalog.foldedNames (catalog : Catalog) : List (List UInt8) :=
  (catalog.filter (!·.isTrigger)).map fun object => object.name.folded

/-- The unique-names rule: no two tables, views or indexes of the catalog have the same folded name
({name}`Catalog.foldedNames` has no duplicate). Triggers are not in the list, so a trigger may
have the name of a table, and two triggers the same name. -/
def Catalog.NamesUnique (catalog : Catalog) : Prop := catalog.foldedNames.Nodup

/-- The affinity of the column at a position, or BLOB for a position outside the list. -/
def columnAffinity (columns : List CatalogColumn) (position : Nat) : Affinity :=
  (columns[position]?.map CatalogColumn.affinity).getD .blob

end Belay.Sqlite.Model
