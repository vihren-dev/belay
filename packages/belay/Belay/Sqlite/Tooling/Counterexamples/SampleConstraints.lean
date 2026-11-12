import Belay.Sqlite.Tooling.Counterexamples.SampleTouched

set_option doc.verso true

/-! Rows that satisfy the simple constraints of a schema. The search changes its selected cells
so that a NOT NULL column gets a value, a foreign key gets a key of its parent, and a table has
no repeated key. Other rules, for example CHECK constraints and collations, stay with
{name}`Belay.Sqlite.Sampling.validated`, which rejects the candidates that break them. -/

namespace Belay.Sqlite.Sampling

open Belay.Sqlite.Model

/-- The selected rows of a table, where a NULL cell of a NOT NULL column becomes the fallback
value. The INTEGER PRIMARY KEY column is not changed, because it gets the rowid. Each row gets
one cell for each column. -/
def notNullCells (table : CatalogTable) (fallback : Value) (rows : List (List Value)) :
    List (List Value) :=
  rows.map fun cells => table.columns.zipIdx.map fun (column, position) =>
    let cell := cells.getD position .null
    if column.notNull && cell matches .null && table.rowidAlias != some position then fallback else cell

/-- The keys of a table whose values two rows must not share: the PRIMARY KEY, unless it is the
rowid alias, which every row gets distinct, and each UNIQUE key. -/
def rowKeys (table : CatalogTable) : List (List Nat) :=
  (if table.primaryKey.isEmpty || table.primaryKey == table.rowidAlias.toList then [] else [table.primaryKey])
    ++ table.uniqueKeys

/-- The selected rows of a table without each row that repeats the stored values
({name}`storedCell`) of a key ({name}`rowKeys`) of an earlier kept row. A key value
with NULL repeats nothing, as in SQLite. Values compare as stored, without collations. -/
def distinctRows (table : CatalogTable) (rows : List (List Value)) : List (List Value) :=
  rows.foldl (fun kept cells =>
    let stored (row : List Value) (index : Nat) (key : List Nat) :=
      key.map fun position => storedCell table index position row
    let repeats := (rowKeys table).any fun key =>
      let values := stored cells kept.length key
      !values.any (· matches .null) && kept.zipIdx.any fun (other, index) => stored other index key == values
    if repeats then kept else kept ++ [cells]) []

/-- The key values of the parent of a foreign key, one for each selected row of the parent:
the stored values of the referenced columns, or of the parent's PRIMARY KEY without a column
list. None when the parent is not a table of the catalog or its key does not match the
columns of the foreign key. -/
def parentKeys (catalog : Catalog) (cells : List (List (List Value))) (key : ForeignKey) :
    List (List Value) :=
  match catalog.zipIdx.find? (·.1.name.sameName key.table) with
  | none => []
  | some ({ entry := .table parent, .. }, position) =>
    let referenced := if key.referenced.isEmpty then parent.primaryKey
      else key.referenced.filterMap fun name => parent.columns.findIdx? (·.name.sameName name)
    if referenced.isEmpty || referenced.length != key.columns.length then []
    else (cells.getD position []).zipIdx.map fun (row, index) =>
      referenced.map fun column => storedCell parent index column row
  | some ({ entry := .index _, .. }, _) | some ({ entry := .trigger _, .. }, _) | some ({ entry := .view _, .. }, _) => []

/-- The selected cells, where each foreign key of a table gets the key values of a parent row
({name}`parentKeys`): row {lit}`i` gets those of parent row {lit}`i` modulo the parent's rows.
A key whose parent has no rows is not changed. -/
def withParentKeys (catalog : Catalog) (cells : List (List (List Value))) : List (List (List Value)) :=
  catalog.zipIdx.map fun (object, position) =>
    let rows := cells.getD position []
    match object.entry with
    | .table table => (allForeignKeys table).foldl (fun rows key =>
        let keys := parentKeys catalog cells key
        if keys.isEmpty then rows else rows.zipIdx.map fun (row, index) =>
          let values := keys.getD (index % keys.length) []
          (key.columns.zip values).foldl (fun row (column, value) => row.set column value) row) rows
    | .index _ | .trigger _ | .view _ => rows

/-- The selected cells with a change applied to the rows of each table; other objects get no
rows. -/
def eachTable (catalog : Catalog) (change : CatalogTable → List (List Value) → List (List Value))
    (cells : List (List (List Value))) : List (List (List Value)) :=
  catalog.zipIdx.map fun (object, position) =>
    match object.entry with
    | .table table => change table (cells.getD position [])
    | .index _ | .trigger _ | .view _ => []

/-- Apply the parent keys ({name}`withParentKeys`), then remove repeated keys
({name}`distinctRows`), until the cells do not change, at most {lit}`fuel` times. A parent that
gets its own key from a grandparent changes the keys of its children in the next round. A round
that removes repeated rows renumbers the rowids of the rest, so the rounds can also run out of
fuel without a cycle of foreign keys; then the last round is the result, and a child can keep a
key that its parent does not have. The candidates are proposals only, so this costs search
quality, not soundness. -/
def settledParentKeys (catalog : Catalog) : (fuel : Nat) → List (List (List Value)) → List (List (List Value))
  | 0, cells => cells
  | fuel + 1, cells =>
    let next := eachTable catalog distinctRows (withParentKeys catalog cells)
    if next == cells then cells else settledParentKeys catalog fuel next

/-- Selected cells that satisfy the simple constraints of the catalog: no NULL in a NOT NULL
column ({name}`notNullCells`), no repeated key ({name}`distinctRows`), and foreign keys with
the keys of their parents, for a bounded number of rounds ({name}`settledParentKeys`).
{name}`validated` checks the result, but it does not check foreign key references, as SQLite
does not without {lit}`PRAGMA foreign_keys`: when the rounds do not settle, a candidate can keep a
key that its parent does not have. -/
def constrainedCells (catalog : Catalog) (fallback : Value) (cells : List (List (List Value))) :
    List (List (List Value)) :=
  let first := eachTable catalog (fun table rows => distinctRows table (notNullCells table fallback rows)) cells
  settledParentKeys catalog (catalog.length + 1) first

end Belay.Sqlite.Sampling
