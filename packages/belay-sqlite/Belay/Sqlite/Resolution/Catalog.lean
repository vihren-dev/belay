import Belay.Sqlite.Declarations
import Belay.Sqlite.Resolution.Syntax
import Belay.Sqlite.Resolution.ColumnDefault
import Belay.Sqlite.Resolution.TypeAffinity
import Belay.Sqlite.Resolution.Keys
import Belay.Sqlite.Resolution.Checks
import Belay.Sqlite.Resolution.ForeignKeys
import Belay.Sqlite.Resolution.StrictTypes
import Belay.Sqlite.Resolution.ReservedNames

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
  /-- The collation of the column ({lit}`COLLATE name`); {lit}`BINARY` without one (ADR 0014,
  D3). -/
  collation : Collation := .binary
  /-- The CHECK constraints of the column definition, in written order; omit them for none
  (ADR 0014, D2). -/
  checks : List CheckConstraint := []
  /-- The foreign keys of the column's {lit}`REFERENCES` constraints, in written order; omit
  them for none (ADR 0014, D2). -/
  foreignKeys : List ForeignKey := []
  /-- How the column is generated; omit it for a column that is not generated (ADR 0014,
  D5). -/
  generated : Option GeneratedColumn := none
  /-- The type of the column in a {lit}`STRICT` table; omit it for a column of another table
  (ADR 0014, D6). -/
  strictType : Option StrictType := none
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
  /-- Whether the table is {lit}`WITHOUT ROWID` (ADR 0014, D4): it has no rowid, its rows
  are in primary-key order, and its key columns are NOT NULL. -/
  withoutRowid : Bool := false
  /-- Whether the table is {lit}`STRICT` (ADR 0014, D6): each column has a
  {name}`CatalogColumn.strictType`. -/
  strict : Bool := false
  /-- The CHECK constraints of the table constraints, in written order; omit them for none
  (ADR 0014, D2). The CHECK constraints of a column are in {name}`CatalogColumn.checks`. -/
  checks : List CheckConstraint := []
  /-- The foreign keys of the {lit}`FOREIGN KEY` table constraints, in written order; omit them
  for none. Those of a column are in {name}`CatalogColumn.foreignKeys`. -/
  foreignKeys : List ForeignKey := []
  deriving Repr, DecidableEq

/-- Every foreign key of the table in the order in which SQLite creates them: those of each
column in column order, then those of the table constraints. {lit}`PRAGMA foreign_key_list`
numbers them in the reverse order. -/
def CatalogTable.allForeignKeys (table : CatalogTable) : List ForeignKey :=
  table.columns.flatMap (·.foreignKeys) ++ table.foreignKeys

/-- Every CHECK constraint of the table: those of each column in column order, then those
of the table constraints. SQLite keeps one list in written order; the two orders differ
only in which label a row reports when several CHECK constraints fail, and every failure
has the same result code. -/
def CatalogTable.allChecks (table : CatalogTable) : List CheckConstraint :=
  table.columns.flatMap (·.checks) ++ table.checks

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

/-- The affinity of a catalog column, from its declared type text; none ({lit}`BLOB`) for an
{lit}`ANY` column of a {lit}`STRICT` table, which stores a value as written. -/
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
