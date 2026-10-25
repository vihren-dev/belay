import Belay.Sqlite.Model.Database

set_option doc.verso true

/-! The facts of an admitted database (ADR 0022, D1 and D2). Each fact is an atom: one fact
about one table, or about the whole database. {lit}`Database.Admitted` bundles them. It describes
every database that SQLite can reach, also through a pragma or a file that bypasses the declared
constraints, so it says nothing about NOT NULL, CHECK or the keys; {lit}`Database.Valid` adds them.
The checks that decide each atom are in {lit}`DatabaseFactChecks`. -/

namespace Belay.Sqlite.Model

/-- For the given property of a table at a catalog position and the given database: at every
position at which {name}`Database.table` gives a table, the property holds for that position
and table. Positions that hold an index, view or trigger, and positions past the end, impose nothing,
so a database without tables satisfies every such property. -/
def Database.EveryTable (property : Nat → Table → Prop) (database : Database) : Prop :=
  ∀ position table, database.table position = some table → property position table

/-- For the given rowid, require both signed 64-bit bounds:
* It is at least negative two to the power 63.
* It is less than two to the power 63. -/
def validRowid (rowid : Int) : Prop := -(2 ^ 63 : Int) ≤ rowid ∧ rowid < 2 ^ 63

/-- For the given columns and row: for every position at which both a column and a
cell exist, the cell equals {name}`Value.store` of itself with the column's affinity.
Positions without a column or without a cell impose nothing. SQLite stores every
value that it writes in this form, so every database that SQLite reaches meets it
(ADR 0012, amendment 1, question 5). -/
def Row.Stored (columns : List CatalogColumn) (row : Row) : Prop :=
  ∀ (position : Nat) (column : CatalogColumn) (value : Value),
    columns[position]? = some column → row.values[position]? = some value →
    Value.store column.affinity value = value

/-- For the given rowid alias and row: when the table has a rowid alias at a position,
the row's cell there is the integer rowid of the row. Without an alias it requires
nothing. SQLite stores an alias as the rowid itself, so every database that SQLite reaches
meets it (ADR 0012, amendment 4, slice 5b). -/
def Row.Aliased (alias : Option Nat) (row : Row) : Prop :=
  ∀ position, alias = some position → row.values[position]? = some (.integer row.rowid)

/-- For the given table: no two of its rows have the same rowid. A table with at most one row
satisfies it. -/
def Table.RowidsDistinct (table : Table) : Prop := (table.rows.map Row.rowid).Nodup

/-- For the given table: the rowid of every row satisfies {name}`validRowid`. A table without
rows satisfies it. -/
def Table.RowidsInRange (table : Table) : Prop := ∀ row ∈ table.rows, validRowid row.rowid

/-- For the given table: every row has exactly one cell for each column of the table's
catalog entry, no fewer and no more. A table without rows satisfies it. -/
def Table.RowsWide (table : Table) : Prop :=
  ∀ row ∈ table.rows, row.values.length = table.shape.columns.length

/-- For the given table: every row is {name}`Row.Stored` for the table's columns. A table
without rows satisfies it. -/
def Table.RowsStored (table : Table) : Prop := ∀ row ∈ table.rows, row.Stored table.shape.columns

/-- For the given table: every row is {name}`Row.Aliased` for the table's rowid alias. A table
without rows, or without a rowid alias, satisfies it. -/
def Table.RowsAliased (table : Table) : Prop := ∀ row ∈ table.rows, row.Aliased table.shape.rowidAlias

/-- The facts of one admitted table, one field for each. A lemma about a write to one table
takes this bundle; {name}`Database.EveryTable` gives each fact for every table. -/
structure Table.Admitted (table : Table) : Prop where
  /-- The table satisfies {name}`Table.RowidsDistinct`: no two rows share a rowid. -/
  rowidsDistinct : table.RowidsDistinct
  /-- The table satisfies {name}`Table.RowidsInRange`: each rowid is a signed 64-bit integer. -/
  rowidsInRange : table.RowidsInRange
  /-- The table satisfies {name}`Table.RowsWide`: each row has one cell for each column. -/
  rowsWide : table.RowsWide
  /-- The table satisfies {name}`Table.RowsStored`: each cell is in its stored form. -/
  rowsStored : table.RowsStored
  /-- The table satisfies {name}`Table.RowsAliased`: a rowid alias cell is the rowid. -/
  rowsAliased : table.RowsAliased

/-- For every table without rows, the table satisfies {name}`Table.Admitted`: each of its facts
is about rows. Proof sketch: each field quantifies over the rows, and with no rows
{lit}`simp` closes it. -/
theorem Table.Admitted.ofEmpty {table : Table} (empty : table.rows = []) : table.Admitted := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Table.RowidsDistinct, Table.RowidsInRange, Table.RowsWide, Table.RowsStored, Table.RowsAliased, empty]

/-- For the given database, require both:
* {lit}`rows` has exactly one entry for each catalog object.
* At every position without a table (an index, view, trigger, or past the end), the stored row
  list is empty. -/
def Database.RowsShaped (database : Database) : Prop :=
  database.rows.length = database.catalog.length ∧
    ∀ position, database.catalog.tableAt position = none → database.rows.getD position [] = []

/-- For the given database: every table satisfies {name}`Table.RowidsDistinct`. -/
def Database.RowidsDistinct (database : Database) : Prop := database.EveryTable fun _ table => table.RowidsDistinct

/-- For the given database: every table satisfies {name}`Table.RowidsInRange`. -/
def Database.RowidsInRange (database : Database) : Prop := database.EveryTable fun _ table => table.RowidsInRange

/-- For the given database: every table satisfies {name}`Table.RowsWide`. -/
def Database.RowsWide (database : Database) : Prop := database.EveryTable fun _ table => table.RowsWide

/-- For the given database: every table satisfies {name}`Table.RowsStored`. -/
def Database.RowsStored (database : Database) : Prop := database.EveryTable fun _ table => table.RowsStored

/-- For the given database: every table satisfies {name}`Table.RowsAliased`. -/
def Database.RowsAliased (database : Database) : Prop := database.EveryTable fun _ table => table.RowsAliased

/-- The facts of an admitted database under a profile, one field for each atom. It holds for
every database that SQLite can reach, also one whose declared constraints fail, and it is the
notion that admits a database (ADR 0012, decision 5). It requires nothing of NOT NULL, CHECK,
the keys or the foreign keys. -/
structure Database.Admitted (profile : Profile) (database : Database) : Prop where
  /-- The catalog satisfies {name}`Catalog.Valid` under the profile's limits. -/
  catalogSupported : database.catalog.Valid profile.limits
  /-- The database satisfies {name}`Database.RowsShaped`. -/
  rowsShaped : database.RowsShaped
  /-- The database satisfies {name}`Database.RowidsDistinct`. -/
  rowidsDistinct : database.RowidsDistinct
  /-- The database satisfies {name}`Database.RowidsInRange`. -/
  rowidsInRange : database.RowidsInRange
  /-- The database satisfies {name}`Database.RowsWide`. -/
  rowsWide : database.RowsWide
  /-- The database satisfies {name}`Database.RowsStored`. -/
  rowsStored : database.RowsStored
  /-- The database satisfies {name}`Database.RowsAliased`. -/
  rowsAliased : database.RowsAliased

/-- For every admitted database and every table at a position of it, the table satisfies
{name}`Table.Admitted`. Proof sketch: each database field holds at every table, so it gives
the table field at the table's position. -/
theorem Database.Admitted.table {database : Database} {position : Nat} {table : Table}
    (admitted : database.Admitted profile)
    (present : database.table position = some table) : table.Admitted :=
  ⟨admitted.rowidsDistinct position table present, admitted.rowidsInRange position table present,
    admitted.rowsWide position table present, admitted.rowsStored position table present,
    admitted.rowsAliased position table present⟩

/-- For every database: if its catalog satisfies {name}`Catalog.Valid` under the profile's
limits, it satisfies {name}`Database.RowsShaped`, and every table satisfies
{name}`Table.Admitted`, then the database satisfies {name}`Database.Admitted`. Proof sketch:
the catalog and row-shape fields are the premises, and each other field takes the same field of
{name}`Table.Admitted` at each table. -/
theorem Database.Admitted.ofTables {database : Database} (catalogSupported : database.catalog.Valid profile.limits)
    (rowsShaped : database.RowsShaped) (tables : database.EveryTable fun _ table => table.Admitted) :
    database.Admitted profile :=
  ⟨catalogSupported, rowsShaped, fun position table present => (tables position table present).rowidsDistinct,
    fun position table present => (tables position table present).rowidsInRange,
    fun position table present => (tables position table present).rowsWide,
    fun position table present => (tables position table present).rowsStored,
    fun position table present => (tables position table present).rowsAliased⟩

/-- For the given profile, catalog and database, require both:
* The database's catalog is the given catalog.
* The database satisfies {name}`Database.Admitted` under the profile. -/
def Conforms (profile : Profile) (catalog : Catalog) (database : Database) : Prop :=
  database.catalog = catalog ∧ database.Admitted profile

end Belay.Sqlite.Model
