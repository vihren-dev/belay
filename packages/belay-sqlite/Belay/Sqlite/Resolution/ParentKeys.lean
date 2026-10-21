import Belay.Sqlite.Resolution.Catalog

set_option doc.verso true

/-! The parent key of a foreign key (ADR 0018, D4), as SQLite's {lit}`sqlite3FkLocateIndex`
finds it: the parent's rowid, or the columns of a unique index of the parent whose columns are
the referenced columns. A foreign key without such a key is SQLite's
{lit}`foreign key mismatch` when a write needs it. -/

namespace Belay.Sqlite

/-- The table at a catalog position, or {lean}`(none : Option CatalogTable)` for a
position that holds an index or is past the end. -/
def Catalog.tableAt (catalog : Catalog) (position : Nat) : Option CatalogTable :=
  match catalog[position]? with
  | some { entry := .table table, .. } => some table
  | some { entry := .index _, .. } | some { entry := .trigger _, .. } => none
  | none => none

/-- Set whether the last foreign key of a table so far is deferred, as
{lit}`sqlite3DeferForeignKey` does: the last key of the table constraints, else the last key of
the last column that has one; a table without a foreign key stays. -/
def CatalogTable.deferLast (table : CatalogTable) (deferred : Bool) : CatalogTable :=
  let setLast (keys : List ForeignKey) := keys.modify (keys.length - 1) fun key => { key with deferred }
  if !table.foreignKeys.isEmpty then { table with foreignKeys := setLast table.foreignKeys }
  else match table.columns.reverse.findIdx? (!·.foreignKeys.isEmpty) with
    | none => table
    | some back =>
      let position := table.columns.length - 1 - back
      { table with columns := table.columns.modify position fun column =>
          { column with foreignKeys := setLast column.foreignKeys } }

/-- How the rows of a foreign key find their parent row. For example, a {lit}`REFERENCES p` of
a parent {lit}`p(id INTEGER PRIMARY KEY)` is {lean}`ParentKey.rowid`. -/
inductive ParentKey where
  /-- The parent's rowid: a key of one column that names the parent's {lit}`INTEGER PRIMARY KEY`,
  or names no column of a parent that has one. -/
  | rowid
  /-- The columns of a unique index of the parent: each pair is a column position of the child
  and the parent column position that it references. -/
  | columns (pairs : List (Nat × Nat))
  deriving Repr, DecidableEq

/-- The column positions and collations of each unique index of a table that a parent key can
use, with whether it is the index of the primary key: the primary key unless it is the rowid
alias, the {lit}`UNIQUE` constraints, and each unique index on the table without a filter whose
terms are all columns. SQLite keeps no index for an {lit}`INTEGER PRIMARY KEY`. -/
def Catalog.parentIndexes (catalog : Catalog) (position : Nat) (table : CatalogTable) :
    List (Bool × List (Nat × Collation)) :=
  let ofColumns (positions : List Nat) :=
    positions.map fun column => (column, (table.columns[column]?.map (·.collation)).getD .binary)
  let primary := if table.primaryKey.isEmpty || (table.rowidAlias.isSome && table.primaryKey == table.rowidAlias.toList)
    then [] else [(true, ofColumns table.primaryKey)]
  primary ++ table.uniqueKeys.map (fun key => (false, ofColumns key)) ++
    catalog.filterMap fun object => match object.entry with
      | .index index =>
        if index.table != position || !index.unique || index.filter.isSome then none
        else (index.keys.mapM fun (key : IndexKey) => match key.term with
          | .column column => some (column, key.collation)
          | .expression _ => none).map (false, ·)
      | .table _ | .trigger _ => none

/-- The pairs of an index that the foreign key's referenced columns name, as
{lit}`sqlite3FkLocateIndex` matches them: the index has one column for each column of the key,
each index column has its column's own collation, and each one is named by a referenced column
(compared by folded name), which gives the child column at the same place. None when an index
column fails. -/
def matchIndex (parent : CatalogTable) (key : ForeignKey) (index : List (Nat × Collation)) :
    Option (List (Nat × Nat)) :=
  if index.length != key.columns.length then none
  else index.mapM fun (column, collation) => do
    let definition ← parent.columns[column]?
    if collation != definition.collation then none
    let place ← key.referenced.findIdx? (·.sameName definition.name)
    let child ← key.columns[place]?
    return (child, column)

/-- The parent key of a foreign key in the parent table at the position
({lit}`sqlite3FkLocateIndex`), or none, which is SQLite's {lit}`foreign key mismatch`:
* a key of one column whose parent has an {lit}`INTEGER PRIMARY KEY` is the rowid when it names
  no column or names that column;
* a key that names no column uses the index of the primary key, with the child columns in key
  order, when the primary key has as many columns as the key;
* a key that names columns uses the first unique index whose columns they name
  ({name}`matchIndex`). -/
def Catalog.parentKey (catalog : Catalog) (position : Nat) (parent : CatalogTable) (key : ForeignKey) :
    Option ParentKey :=
  let aliasNamed := match parent.rowidAlias, key.referenced with
    | some _, [] => true
    | some alias, [name] => (parent.columns[alias]?).any (·.name.sameName name)
    | some _, _ :: _ :: _ | none, _ => false
  if key.columns.length == 1 && aliasNamed then some .rowid
  else
    let indexes := catalog.parentIndexes position parent
    if key.referenced.isEmpty then
      (indexes.find? (·.1)).bind fun (_, index) =>
        if index.length == key.columns.length then some (.columns (key.columns.zip (index.map (·.1)))) else none
    else (indexes.findSome? fun (_, index) => matchIndex parent key index).map .columns

/-- What a foreign key of the catalog refers to: the parent table at a position with its parent
key, a parent table without one, or no table of its name. -/
inductive ParentLink where
  /-- The parent table and its parent key. -/
  | located (position : Nat) (key : ParentKey)
  /-- The parent table exists, but has no parent key for the foreign key
  ({lit}`foreign key mismatch`). -/
  | mismatch (position : Nat)
  /-- No table has the name that the foreign key references. -/
  | missing
  deriving Repr, DecidableEq

/-- One foreign key of the catalog: the position of its child table, the key, and what it
refers to. -/
structure ForeignKeyLink where
  /-- The catalog position of the table that has the foreign key. -/
  child : Nat
  /-- The foreign key. -/
  key : ForeignKey
  /-- The parent table and key that it refers to. -/
  parent : ParentLink
  deriving Repr, DecidableEq

/-- The parent link of a foreign key in the catalog. -/
def Catalog.parentLink (catalog : Catalog) (key : ForeignKey) : ParentLink :=
  match catalog.findTable key.table with
  | none => .missing
  | some (position, parent) => match catalog.parentKey position parent key with
    | some found => .located position found
    | none => .mismatch position

/-- Every foreign key of the catalog in the order in which SQLite creates them: the tables in
catalog order and the keys of each in {name}`CatalogTable.allForeignKeys` order. -/
def Catalog.foreignKeyLinks (catalog : Catalog) : List ForeignKeyLink :=
  catalog.zipIdx.flatMap fun (object, position) => match object.entry with
    | .table table => table.allForeignKeys.map fun key => { child := position, key, parent := catalog.parentLink key }
    | .index _ | .trigger _ => []

/-- The foreign keys of the table at the position, newest first, as SQLite keeps them in the
table's list. -/
def childLinks (links : List ForeignKeyLink) (position : Nat) : List ForeignKeyLink :=
  (links.filter (·.child == position)).reverse

/-- The foreign keys that reference the table at the position, newest first, as SQLite keeps
them in the schema's list of references: those with a parent key, and those without one
({name}`ParentLink.mismatch`). -/
def parentLinks (links : List ForeignKeyLink) (position : Nat) : List ForeignKeyLink :=
  (links.filter fun link => match link.parent with
    | .located parent _ | .mismatch parent => parent == position
    | .missing => false).reverse

end Belay.Sqlite
