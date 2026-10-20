import Belay.Sqlite.Declarations
import Belay.Sqlite.Resolution.Syntax
import Belay.Sqlite.Resolution.ColumnDefault
import Belay.Sqlite.Resolution.TypeAffinity
import Belay.Sqlite.Resolution.Keys

set_option doc.verso true

/-! The catalog that name resolution reads and updates. Tables and indexes share
one namespace, as in {lit}`sqlite_schema`. Names keep their case as written;
lookup compares SQLite's ASCII-folded form ({name}`Belay.Sqlite.Identifier.sameName`).
Columns keep their declared type text, and the affinity function
({lit}`affinityOf`, in {lit}`TypeAffinity.lean`) computes the affinity from it. -/

namespace Belay.Sqlite

/-- One catalog column. Supply the name and declared type as written; omit the
constraint fields for a nullable column without a default. -/
structure CatalogColumn where
  /-- The column name as written, for example {lit}`Id`. -/
  name : Identifier
  /-- The declared type text, or {lean}`(none : Option String)` for no type. -/
  declaredType : Option String
  /-- Whether the column declares NOT NULL. -/
  notNull : Bool := false
  /-- The {lit}`ON CONFLICT` algorithm of the NOT NULL constraint; ABORT without one. -/
  notNullAlgorithm : ConflictAlgorithm := .abort
  /-- The resolved DEFAULT with its source spelling ({name}`ColumnDefault`); omit it for no
  default. -/
  defaultValue : Option ColumnDefault := none
  deriving Repr, DecidableEq

/-- One table entry. Keys are lists of column positions. Use
{lean}`(none : Option Nat)` for {name}`CatalogTable.rowidAlias` when no column is
an alias for the rowid. -/
structure CatalogTable where
  /-- The columns in table order. -/
  columns : List CatalogColumn
  /-- The primary-key column positions in key order; empty for no primary key. -/
  primaryKey : List Nat := []
  /-- The position of the column that is an alias for the rowid, if any. -/
  rowidAlias : Option Nat := none
  /-- Whether SQLite's implicit key index of the primary key is descending: the key is
  declared {lit}`PRIMARY KEY DESC` on its column and has no earlier UNIQUE constraint of
  the same column, whose ascending index SQLite keeps. Use {lean}`false` for any other key. -/
  primaryKeyDescending : Bool := false
  /-- The {lit}`ON CONFLICT` algorithm of the primary key, none without the clause. -/
  primaryKeyAlgorithm : Option ConflictAlgorithm := none
  /-- The column positions of each UNIQUE constraint, in written order. -/
  uniqueKeys : List (List Nat) := []
  /-- The {lit}`ON CONFLICT` algorithm of each UNIQUE constraint, in the order of
  {lit}`uniqueKeys`, none without the clause; a constraint without an entry has none. -/
  uniqueAlgorithms : List (Option ConflictAlgorithm) := []
  deriving Repr, DecidableEq

/-- The {lit}`ON CONFLICT` algorithm of the UNIQUE constraint at the position, none for a
constraint without the clause or without an entry. -/
def CatalogTable.uniqueAlgorithm (table : CatalogTable) (index : Nat) : Option ConflictAlgorithm :=
  table.uniqueAlgorithms.getD index none

/-- The algorithms of the UNIQUE constraints, one for each key of
{name}`CatalogTable.uniqueKeys`. -/
def CatalogTable.keyedUniqueAlgorithms (table : CatalogTable) : List (Option ConflictAlgorithm) :=
  table.uniqueKeys.mapIdx fun index _ => table.uniqueAlgorithm index

/-- The kind and content of one catalog object. -/
inductive CatalogEntry where
  /-- A table. -/
  | table (table : CatalogTable)
  /-- An index. -/
  | index (index : CatalogIndex)
  deriving Repr, DecidableEq

/-- One named catalog object. The name is kept as written; lookup folds it. -/
structure CatalogObject where
  /-- The object name as written. -/
  name : Identifier
  /-- The object's kind and content. -/
  entry : CatalogEntry
  deriving Repr, DecidableEq

/-- The catalog: all objects in creation order. Positions are list indexes.
{lean}`([] : Catalog)` is the empty catalog. -/
abbrev Catalog := List CatalogObject

/-- The first position whose element satisfies the test, with the element. -/
def findPosition (test : α → Bool) : List α → Option (Nat × α)
  | [] => none
  | item :: rest => if test item then some (0, item) else
      (findPosition test rest).map fun (position, found) => (position + 1, found)

/-- The first catalog object whose folded name equals the folded given name. -/
def Catalog.find (catalog : Catalog) (name : Identifier) : Option (Nat × CatalogObject) :=
  findPosition (fun object => object.name.sameName name) catalog

/-- The first object with the folded name, when it is a table: its position and entry. -/
def Catalog.findTable (catalog : Catalog) (name : Identifier) : Option (Nat × CatalogTable) :=
  match catalog.find name with
  | some (position, { entry := .table table, .. }) => some (position, table)
  | some (_, { entry := .index _, .. }) => none
  | none => none

/-- The columns of the table with the name in the catalog, in table order, or
{lean}`(none : Option (List CatalogColumn))` when no table has the name. Use it to
state catalog requirements. -/
def Catalog.columnsOf (catalog : Catalog) (name : Identifier) : Option (List CatalogColumn) :=
  (catalog.findTable name).map (·.2.columns)

/-- The position of the first column whose folded name equals the folded given name. -/
def columnPosition (columns : List CatalogColumn) (name : Identifier) : Option Nat :=
  (findPosition (fun column => column.name.sameName name) columns).map Prod.fst

/-- The affinity of a catalog column, from its declared type text. -/
def CatalogColumn.affinity (column : CatalogColumn) : Affinity := affinityOf column.declaredType

/-- Each unique key of the table at a catalog position, in this order: the primary key
when there is one, the UNIQUE constraints, and the unique indexes on the table in
catalog order. SQLite keeps each of them as an index, and a write that makes two rows
equal on one of them fails. -/
def Catalog.uniqueKeys (catalog : Catalog) (position : Nat) (table : CatalogTable) : List UniqueKey :=
  ((if table.primaryKey.isEmpty then [] else [table.primaryKey]) ++ table.uniqueKeys).map UniqueKey.ofColumns ++
    catalog.filterMap fun object => match object.entry with
      | .index index => if index.table == position && index.unique then some index.uniqueKey else none
      | .table _ => none

/-- Add the table with the name at the end of the catalog, at position
{lean}`catalog.length`, as CREATE TABLE does. The resolver and the execution of CREATE
TABLE both use it, so they give the same catalog. -/
def Catalog.createTable (catalog : Catalog) (name : Identifier) (table : CatalogTable) : Catalog :=
  catalog ++ [{ name, entry := .table table }]

/-- Add the index with the name at the end of the catalog, as CREATE INDEX does. -/
def Catalog.createIndex (catalog : Catalog) (name : Identifier) (index : CatalogIndex) : Catalog :=
  catalog ++ [{ name, entry := .index index }]

/-- Append the column to the table at the position, keeping the table's name and every
other object, as ALTER TABLE ADD COLUMN does. A position that holds an index or no
object is unchanged. The resolver and the execution of ADD COLUMN both use it. -/
def Catalog.addColumn (catalog : Catalog) (position : Nat) (column : CatalogColumn) : Catalog :=
  match catalog[position]? with
  | some { name, entry := .table table } =>
    catalog.set position { name, entry := .table { table with columns := table.columns ++ [column] } }
  | some { entry := .index _, .. } => catalog
  | none => catalog

/-- Whether the folded name starts with {lit}`sqlite_`, which SQLite reserves. -/
def reservedName (name : Identifier) : Bool := (bytes! "sqlite_").isPrefixOf name.folded

/-- The column names of SQLite's statistics tables, which a schema may contain, by the
folded table name ({name}`Identifier.folded`). -/
def statisticsColumns (folded : List UInt8) : Option (List Identifier) :=
  if folded == bytes! "sqlite_stat1" then some [name! "tbl", name! "idx", name! "stat"]
  else if folded == bytes! "sqlite_stat4" then
    some [name! "tbl", name! "idx", name! "neq", name! "nlt", name! "ndlt", name! "sample"]
  else none

/-- Whether a column name is one of SQLite's rowid names, which the model keeps
for the physical rowid. -/
def rowidName (name : Identifier) : Bool :=
  [bytes! "rowid", bytes! "_rowid_", bytes! "oid"].contains name.folded

/-- The folded names of all catalog objects, in catalog order. -/
def Catalog.foldedNames (catalog : Catalog) : List (List UInt8) :=
  catalog.map fun object => object.name.folded

/-- No two catalog objects have the same folded name. The empty catalog has
unique names. -/
def Catalog.NamesUnique (catalog : Catalog) : Prop := catalog.foldedNames.Nodup

/-- The affinity of the column at a position, or BLOB for a position outside the list. -/
def columnAffinity (columns : List CatalogColumn) (position : Nat) : Affinity :=
  (columns[position]?.map CatalogColumn.affinity).getD .blob

end Belay.Sqlite
