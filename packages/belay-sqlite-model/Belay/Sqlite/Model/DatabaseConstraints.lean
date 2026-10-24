import Belay.Sqlite.Model.DatabaseFacts
import Belay.Sqlite.Model.LiteralData

set_option doc.verso true

/-! The facts of a valid database (ADR 0022, D1 and D2): the declared constraints hold. Each
fact is stated with the functions that the model's writes check ({lit}`LiteralData.constraints`),
so a valid database is one that the writes accept. {lit}`Database.Valid` bundles them with the
facts of an admitted database. SQLite keeps them for the databases that it writes with its
statements, but not after a pragma or a file that bypasses them, so {lit}`Database.Admitted`,
not {lit}`Database.Valid`, admits a database. The checks are in {lit}`DatabaseConstraintChecks`. -/

namespace Belay.Sqlite.Model

/-- For the given table: in every row, at every position at which both a column and a cell
exist, a column with NOT NULL holds no NULL. Positions without a column or a cell impose
nothing; {name}`Table.RowsWide` excludes them. A table without rows satisfies it. -/
def Table.NotNull (table : Table) : Prop :=
  ∀ row ∈ table.rows, ∀ (position : Nat) (column : CatalogColumn) (value : Value),
    table.shape.columns[position]? = some column → row.values[position]? = some value →
    column.notNull = true → value ≠ .null

/-- For the given table: in every row, at every position at which both a column and a cell
exist, the cell fits the column's {lit}`STRICT` type when the column has one
({name}`StrictType.fits`). A column without a strict type takes every value, and a table
without rows satisfies it. -/
def Table.TypesFit (table : Table) : Prop :=
  ∀ row ∈ table.rows, ∀ (position : Nat) (column : CatalogColumn) (value : Value),
    table.shape.columns[position]? = some column → row.values[position]? = some value →
    column.strictType.all (·.fits value) = true

/-- For the given table: every row satisfies every CHECK constraint of the table
({name}`CatalogTable.allChecks`), which means that its condition is not false on the row
({name}`LiteralData.checkHolds`; NULL passes). A table without CHECK constraints or without rows
satisfies it. -/
def Table.ChecksHold (table : Table) : Prop :=
  ∀ row ∈ table.rows, ∀ check ∈ table.shape.allChecks, LiteralData.checkHolds row check = true

/-- For the given keys and table: for every key, no two rows of the table, in either order of
the list, conflict on it ({name}`LiteralData.keyEqual`). Two rows with a NULL in the key do not
conflict, nor do two rows of a partial index whose filter is false or NULL for one of them.
With no keys or with at most one row it holds. -/
def Table.KeysUnique (keys : List UniqueKey) (table : Table) : Prop :=
  ∀ key ∈ keys, table.rows.Pairwise fun first second => LiteralData.keyEqual key first second = false

/-- For the given database: every table satisfies {name}`Table.NotNull`. -/
def Database.NotNull (database : Database) : Prop := database.EveryTable fun _ table => table.NotNull

/-- For the given database: every table satisfies {name}`Table.TypesFit`. -/
def Database.TypesFit (database : Database) : Prop := database.EveryTable fun _ table => table.TypesFit

/-- For the given database: every table satisfies {name}`Table.ChecksHold`. -/
def Database.ChecksHold (database : Database) : Prop := database.EveryTable fun _ table => table.ChecksHold

/-- For the given database: every table satisfies {name}`Table.KeysUnique` for its unique keys
in the catalog ({name}`Catalog.uniqueKeys`): its PRIMARY KEY, its UNIQUE constraints and the
unique indexes on it, with their filters, terms and collations. -/
def Database.KeysUnique (database : Database) : Prop :=
  database.EveryTable fun position table => table.KeysUnique (database.catalog.uniqueKeys position table.shape)

/-- The facts of a valid database under a profile: the facts of an admitted database, and the
declared constraints of every table hold. Foreign-key row references and parent-schema compatibility are separate facts
({lit}`Database.RowReferencesHold` and {lit}`Database.ParentSchemasCompatible`). A claim about every database that SQLite writes with its
statements states it as a hypothesis; it admits no database. -/
structure Database.Valid (profile : Profile) (database : Database) : Prop where
  /-- The database satisfies {name}`Database.Admitted` under the profile. -/
  admitted : database.Admitted profile
  /-- The database satisfies {name}`Database.NotNull`. -/
  notNull : database.NotNull
  /-- The database satisfies {name}`Database.ChecksHold`. -/
  check : database.ChecksHold
  /-- The database satisfies {name}`Database.TypesFit`. -/
  typesFit : database.TypesFit
  /-- The database satisfies {name}`Database.KeysUnique`. -/
  unique : database.KeysUnique

/-- For every valid database, no two rows of a table share a rowid
({name}`Database.RowidsDistinct`). -/
theorem Database.Valid.rowid_unique {database : Database} (valid : database.Valid profile) :
    database.RowidsDistinct :=
  valid.admitted.rowidsDistinct

end Belay.Sqlite.Model
