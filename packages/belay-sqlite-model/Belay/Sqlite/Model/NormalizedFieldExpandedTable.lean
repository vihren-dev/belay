import Belay.Sqlite.Model.NormalizedFieldExpansion
import Belay.Sqlite.Model.NormalizedFieldSelectResolution
import Belay.Sqlite.Model.ResolveNamesBelow

set_option doc.verso true

/-! The table that a lowercase-field expansion leaves at the target position and its
catalog lookup, read from {lit}`expandedDatabase`. -/

namespace Belay.Sqlite.Model.NormalizedField
open Resolved

/-- The target table after the expansion: the original shape with the plain TEXT field
appended, and the rows of {name}`loweredRows`. -/
def expandedTable (table : Table) (name : Identifier) (source : Nat) : Table :=
  { shape := { table.shape with columns := table.shape.columns ++ [textColumn name table.shape.strict] },
    rows := loweredRows table source }

/-- For every database with a table at an aligned position, the expansion leaves the table
{name}`expandedTable` at that position. The two appended trigger objects change no position of
the table and no stored rows. Proof sketch: ADD COLUMN and the row replacement give the table
({name}`Database.table_addColumn`, {name}`Database.table_setRows`), and each appended object keeps
it ({name}`Database.table_append`). -/
theorem expandedDatabase_table {database : Database} {position source : Nat} {table : Table}
    (name : Identifier) (first second : Identifier × CatalogTrigger)
    (present : database.table position = some table) (aligned : position < database.rows.length) :
    (expandedDatabase database position source table name first second).table position =
      some (expandedTable table name source) := by
  have added := Database.table_addColumn (textColumn name table.shape.strict) .null present
  have alignedAdded : position < (database.addColumn position (textColumn name table.shape.strict) .null).rows.length := by
    simpa [Database.addColumn] using aligned
  have stored := Database.table_setRows (loweredRows table source) added alignedAdded
  have appendedFirst := Database.table_append
    { name := first.1, entry := .trigger first.2 } stored
  have appendedSecond := Database.table_append { name := second.1, entry := .trigger second.2 } appendedFirst
  simpa [expandedDatabase, withTrigger, Catalog.createTrigger, expandedTable, Table.appendColumns] using appendedSecond

/-- For every catalog lookup of the target table by name, the expansion's catalog finds the
same position with the extended shape. Triggers are not in the table namespace. Proof sketch:
{name}`findTable_addColumn` for the added field, then {name}`findTable_createTrigger` for each
appended trigger. -/
theorem expandedDatabase_findTable {database : Database} {tableName : Identifier} {position source : Nat}
    {table : Table} (name : Identifier) (first second : Identifier × CatalogTrigger)
    (found : database.catalog.findTable tableName = some (position, table.shape)) :
    (expandedDatabase database position source table name first second).catalog.findTable tableName =
      some (position, (expandedTable table name source).shape) := by
  simp only [expandedDatabase, withTrigger, Database.setRows, Database.addColumn, findTable_createTrigger]
  exact findTable_addColumn (textColumn name table.shape.strict) found

/-- For every original table with wide aliased rows, in-range primary-key and source positions
and plain original columns, the full scan of the expanded table is the scan of the original with
the lowercase of its source cell appended to each row. Proof sketch: the actual backfill UPDATE
computes the rows of {name}`loweredRows` ({name}`updated_lower_append`), and
{name}`sourceRows_updated_lower` transports the scan. -/
theorem sourceRows_expandedTable (table : Table) (name : Identifier) (source : Nat)
    (wide : table.RowsWide) (aliased : table.RowsAliased) (inside : source < table.shape.columns.length)
    (keysInside : ∀ position ∈ table.shape.primaryKey, position < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none) :
    sourceRows (expandedTable table name source) =
      (sourceRows table).map fun row => row ++ [mapText lowerByte (row.getD source .null)] := by
  have text : (textColumn name table.shape.strict).affinity = .text := by cases table.shape.strict <;> rfl
  have rows := updated_lower_append (EvalContext.plain 0) table (textColumn name table.shape.strict) source wide
    aliased inside plain rfl text
  have equal : LiteralData.updated (EvalContext.plain 0)
      (table.appendColumns [(textColumn name table.shape.strict, .null)])
      [(table.shape.columns.length, .scalar .lower (.cons (.column source) .nil))] none =
      expandedTable table name source :=
    congrArg (fun rows : List Row => ({ shape := (expandedTable table name source).shape, rows } : Table)) rows
  rw [← equal]
  exact sourceRows_updated_lower (EvalContext.plain 0) table _ source wide aliased inside keysInside plain rfl text

end Belay.Sqlite.Model.NormalizedField
