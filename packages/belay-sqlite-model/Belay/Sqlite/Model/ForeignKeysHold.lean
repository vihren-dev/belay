import Belay.Sqlite.Model.ForeignKeyPhases
import Belay.Sqlite.Model.DatabaseFactChecks

set_option doc.verso true

/-! The fact that the foreign keys of a database hold (ADR 0022, D1). It is outside
{lit}`Database.Valid`: with foreign keys off, SQLite stores a child row without its parent, so
the statements of a valid database can break it. A child row is satisfied as the writes check
it ({lit}`ForeignKeyPhases`): with a NULL in its key, or with a parent row that the key finds
({name}`Belay.Sqlite.Model.parentFound`). The fact covers every key of the catalog, also a deferred one. -/

namespace Belay.Sqlite.Model

/-- Whether a child row of a foreign key has what the key requires in the database: a NULL in
its key ({name}`ForeignKeyLink.hasNull`), or a row of the parent table that the key finds
({name}`parentFound`). A key whose parent table does not exist, or has no parent key
({name}`ParentLink.missing`, {name}`ParentLink.mismatch`), finds no parent row. -/
def ForeignKeyLink.satisfied (database : Database) (link : ForeignKeyLink) (row : Row) : Bool :=
  link.hasNull row.values || match link.parent with
    | .located parent key => match database.catalog.tableAt parent with
      | some shape => parentFound shape key link row.values (database.rowsAt parent) none
      | none => false
    | .mismatch _ | .missing => false

/-- For the given database, position and table: for every foreign key of the table at the
position ({name}`childLinks` of {name}`Catalog.foreignKeyLinks`) and every row of the table,
{name}`ForeignKeyLink.satisfied` holds. A table without foreign keys or without rows satisfies
it. -/
def Table.ForeignKeysHold (database : Database) (position : Nat) (table : Table) : Prop :=
  ∀ link ∈ childLinks database.catalog.foreignKeyLinks position, ∀ row ∈ table.rows, link.satisfied database row = true

/-- For the given database: every table satisfies {name}`Table.ForeignKeysHold`. A database
without foreign keys satisfies it. -/
def Database.ForeignKeysHold (database : Database) : Prop :=
  database.EveryTable fun position table => Table.ForeignKeysHold database position table

/-- Check {name}`Table.ForeignKeysHold` for the table at a position of the database. -/
def Table.foreignKeysHold (database : Database) (position : Nat) (table : Table) : Bool :=
  (childLinks database.catalog.foreignKeyLinks position).all fun link => table.rows.all (link.satisfied database)

/-- For every database, position and table, {name}`Table.foreignKeysHold` is {lean}`true`
exactly when {name}`Table.ForeignKeysHold` holds. -/
theorem Table.foreignKeysHold_iff (database : Database) (position : Nat) (table : Table) :
    table.foreignKeysHold database position = true ↔ table.ForeignKeysHold database position := by
  simp [Table.foreignKeysHold, Table.ForeignKeysHold]

/-- Decide {name}`Database.ForeignKeysHold` with {name}`Table.foreignKeysHold`. -/
instance Database.decidableForeignKeysHold (database : Database) : Decidable database.ForeignKeysHold :=
  database.decideEveryTable (fun position table => table.foreignKeysHold database position)
    fun position table => Table.foreignKeysHold_iff database position table

end Belay.Sqlite.Model
