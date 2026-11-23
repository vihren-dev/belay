import Belay

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_schema_script_test.py` (statement rule pilot, "Client claims"): the
site of the client claims of {lit}`ItemInsertClaims`. The table {lit}`items` has an INTEGER PRIMARY KEY, which is
the rowid alias, and a TEXT column. The statement {lit}`INSERT INTO items VALUES ($id, $name)` stores one row with
the two values. The facts here are about functions on databases, tables and rows of the model; none of them is
about the step of a statement. They check that the data functions of the kind rule of plain INSERT are usable in
proofs on a fixed catalog with arbitrary rows. -/

namespace ItemInsertSite
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- A database with one table {lit}`items` and no rows. -/
def itemsSchema : Database := db! r"CREATE TABLE items(id INTEGER PRIMARY KEY, name TEXT);"

/-- The catalog of {name}`itemsSchema`. -/
def itemsCatalog : Catalog := itemsSchema.raw.catalog

/-- The catalog entry of {lit}`items`: the columns {lit}`id` and {lit}`name`, the primary key on {lit}`id`, and
{lit}`id` as the rowid alias. -/
def itemsShape : CatalogTable :=
  { columns := [{ name := name! "id", declaredType := some "INTEGER" }, { name := name! "name", declaredType := some "TEXT" }],
    primaryKey := [0], rowidAlias := some 0 }

/-- The program text that inserts one item with the id and the name. -/
def insertItem (id : Int64) (name : String) : Script := sql r"INSERT INTO items VALUES ($id, $name)"

/-- The resolved cells of {name}`insertItem`: the two parameters. -/
abbrev itemCells : List (List Resolved.Cell) := [[.expression (.parameter 1), .expression (.parameter 2)]]

/-- The table {lit}`items` with the first row list of a database. -/
abbrev itemsTable (rows : List (List Row)) : Table := ⟨itemsShape, rows.getD 0 []⟩

/-- The cells of a new item: the id as an integer and the name as text. -/
def itemValues (id : Int64) (name : String) : List Value := [.integer id.toInt, .text name.toUTF8.toList]

/-- The stored row of a new item: the id is the rowid. -/
def itemRow (id : Int64) (name : String) : Row := ⟨id.toInt, itemValues id name⟩

/-- The catalog {name}`itemsCatalog` has exactly one entry: the table {lit}`items` with {name}`itemsShape`. Proof:
the kernel evaluates the parsed schema. -/
theorem items_catalog : itemsCatalog = [{ name := name! "items", entry := .table itemsShape }] := by decide +kernel

/-- For every row lists: the database with {name}`itemsCatalog` has the table {name}`itemsTable` at position 0.
Proof: {name}`items_catalog` makes the lookup compute. -/
theorem items_table (rows : List (List Row)) :
    ({ catalog := itemsCatalog, rows } : Model.Database).table 0 = some (itemsTable rows) := by
  rw [items_catalog]
  rfl

/-- The insert of {name}`itemCells` reads no counter. -/
theorem items_reads : (Resolved.Statement.insert 0 itemCells [] [] none).counterReads = [] := by decide +kernel

/-- For every clock and index: the insert of {name}`itemCells` reads no clock, so its clock value is 0. -/
theorem items_clock (clock : Option Clock) (index : Nat) :
    statementClock clock index (.insert 0 itemCells [] [] none) = some 0 := rfl

/-- The column {lit}`id` has INTEGER affinity. -/
theorem items_id_integer :
    ({ name := name! "id", declaredType := some "INTEGER" } : CatalogColumn).affinity = .integer := by decide

/-- The column {lit}`name` has TEXT affinity. -/
theorem items_name_text :
    ({ name := name! "name", declaredType := some "TEXT" } : CatalogColumn).affinity = .text := by decide

/-- For every clock value, counters, database, id and name: the rows of {name}`itemCells` with the two values as
parameters are the one row {name}`itemValues`. The affinities keep both values. Proof: the cells are the two
parameters, and the INTEGER and TEXT affinities store an integer and a text value unchanged. -/
theorem items_values (value : Int) (counters : Counters) (database : Model.Database) (id : Int64) (name : String) :
    Resolved.rowsAt (Resolved.statementContext value counters [.integer id.toInt, .text name.toUTF8.toList] database [])
      itemsShape.columns itemCells = [itemValues id name] := by
  rw [itemCells, itemsShape, rowsAt_two_parameters, items_id_integer, items_name_text]
  simp [Value.store, boundValue, numericStore, itemValues]

/-- No column of {name}`itemsShape` is generated. -/
theorem items_plain : ∀ column ∈ itemsShape.columns, column.generated = none := by decide

/-- For every row lists, id and name: inserting {name}`itemValues` into {name}`itemsTable` appends {name}`itemRow`
to the old rows. The alias cell gives the rowid. Proof: no column is generated, so the insert appends one row
whose rowid is the integer in the alias cell. -/
theorem items_inserted (rows : List (List Row)) (id : Int64) (name : String) :
    (LiteralData.inserted (itemsTable rows) [itemValues id name]).rows = rows.getD 0 [] ++ [itemRow id name] := by
  rw [itemValues, LiteralData.inserted_plain _ _ _ items_plain (.inr rfl)]
  simp [LiteralData.newRowid, itemsShape, itemRow, itemValues]

/-- For every row lists: the unique keys of {lit}`items` are the one key of its primary key. Proof:
{name}`items_catalog` makes the key list compute. -/
theorem items_keys (rows : List (List Row)) :
    ({ catalog := itemsCatalog, rows } : Model.Database).keys 0 (itemsTable rows) =
      [UniqueKey.ofColumns itemsShape.columns [0]] := by
  rw [items_catalog]
  rfl

/-- For every row lists, id and name: the alias cell of {name}`itemValues` is an integer, so no row has an alias
that SQLite refuses. -/
theorem items_aliases (rows : List (List Row)) (id : Int64) (name : String) :
    [itemValues id name].findIdx? (LiteralData.aliasMismatch (itemsTable rows).shape) = none := rfl

/-- For every evaluation context: no cell of {name}`itemCells` can fail. -/
theorem items_cellsReady (context : Resolved.EvalContext) : Resolved.cellsReady context itemCells = true := rfl

/-- For every row lists, id, name, database and keys: the counts of a successful insert of {name}`itemValues` are
one changed row, one row in the total, and the id as the last inserted rowid. Proof: {name}`items_inserted` gives
the last row, whose rowid is the id. -/
theorem items_counts_ok (rows : List (List Row)) (id : Int64) (name : String) (database : Model.Database)
    (keys : List UniqueKey) :
    LiteralData.insertCounts (.ok database) keys (itemsTable rows) [itemValues id name] =
      { changes := some 1, total := 1, lastRowid := some id.toInt } := by
  simp [LiteralData.insertCounts, LiteralData.lastInsertedRowid, items_inserted, itemsShape, itemRow]

end ItemInsertSite
