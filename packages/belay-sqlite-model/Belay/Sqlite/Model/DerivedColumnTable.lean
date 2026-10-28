import Belay.Sqlite.Model.DerivedColumnBackfill
import Belay.Sqlite.Model.CatalogAddColumnSearch
import Belay.Sqlite.Model.CatalogTriggerSearch
import Belay.Sqlite.Model.ResolveCreateIndexCatalog
import Belay.Sqlite.Model.DatabaseLookup

set_option doc.verso true

/-! The database that "add a column, backfill it from an expression, register triggers" leaves
(ADR 0017, S6). The definitions state the reached table, rows and catalog; the laws read the table, the
catalog entry and the scan of the table from them. No law here assumes a row relation: the next module
proves that the actual statements store exactly these rows. -/

namespace Belay.Sqlite.Model
open Resolved

/-- Whether the value of an expression does not depend on the context in which it is evaluated: the clock,
the parameters, the counters and the subqueries. For example, {lit}`lower(a)` is context-free, and
{lit}`a + ?1` is not. A stored expression must be context-free, because the backfill evaluates it in the
context of one statement and a lookup evaluates it in the context of another. -/
def Resolved.Expr.ContextFree (expression : Resolved.Expr) : Prop :=
  ∀ (first second : EvalContext) (cells : List Value), expression.eval first cells = expression.eval second cells

/-- The table with a column appended whose cell in each row is the stored value of an expression of the
row's old cells. The expression is evaluated in the plain context {lit}`EvalContext.plain 0`; for a
context-free expression ({name}`Resolved.Expr.ContextFree`) that is the value in every context. The value
goes through the affinity of the column. Rows keep their order and rowids. -/
def Table.addDerivedColumn (table : Table) (column : CatalogColumn) (derived : Resolved.Expr) : Table :=
  { shape := { table.shape with columns := table.shape.columns ++ [column] },
    rows := table.rows.map fun row =>
      row.appendValues [Value.store column.affinity (derived.eval (EvalContext.plain 0) row.values)] }

/-- Register one trigger as CREATE TRIGGER does: append the trigger object to the catalog and an empty
storage slot to the rows. -/
def Database.appendTrigger (database : Database) (name : Identifier) (trigger : CatalogTrigger) : Database :=
  { catalog := database.catalog.createTrigger name trigger, rows := database.rows ++ [[]] }

/-- The database after ADD COLUMN of a column at a table's position, a backfill of the column from an
expression, and the registration of the triggers in order: the rows of the table are replaced by
{name}`Table.addDerivedColumn`, and each trigger object is appended. -/
def Database.addDerivedColumn (database : Database) (position : Nat) (table : Table) (column : CatalogColumn)
    (derived : Resolved.Expr) (triggers : List (Identifier × CatalogTrigger)) : Database :=
  triggers.foldl (fun database trigger => database.appendTrigger trigger.1 trigger.2)
    ((database.addColumn position column .null).setRows position (table.addDerivedColumn column derived).rows)

/-- For every database and list of triggers, appending the triggers keeps the table at every position that
has a table. Proof sketch: induction over the triggers; one appended trigger keeps every table
({name}`Database.table_append`). -/
theorem Database.table_appendTriggers {database : Database} {position : Nat} {table : Table}
    (triggers : List (Identifier × CatalogTrigger)) (present : database.table position = some table) :
    (triggers.foldl (fun database trigger => database.appendTrigger trigger.1 trigger.2) database).table position =
      some table := by
  induction triggers generalizing database with
  | nil => exact present
  | cons trigger rest ih =>
    exact ih (Database.table_append { name := trigger.1, entry := .trigger trigger.2 } present)

/-- For every database with a table at an aligned position, the migration leaves
{name}`Table.addDerivedColumn` at that position, whatever triggers it appends. Proof sketch: ADD COLUMN and
the row replacement give the table ({name}`Database.table_addColumn`, {name}`Database.table_setRows`), and
the appended triggers keep it ({name}`Database.table_appendTriggers`). -/
theorem Database.table_addDerivedColumn {database : Database} {position : Nat} {table : Table}
    (column : CatalogColumn) (derived : Resolved.Expr) (triggers : List (Identifier × CatalogTrigger))
    (present : database.table position = some table) (aligned : position < database.rows.length) :
    (database.addDerivedColumn position table column derived triggers).table position =
      some (table.addDerivedColumn column derived) := by
  have added := Database.table_addColumn column .null present
  have alignedAdded : position < (database.addColumn position column .null).rows.length := by
    simpa [Database.addColumn] using aligned
  have stored := Database.table_setRows (table.addDerivedColumn column derived).rows added alignedAdded
  exact Database.table_appendTriggers triggers (by simpa [Table.addDerivedColumn, Table.appendColumns] using stored)

/-- For every catalog and list of triggers, appending the triggers keeps every table lookup by name. Proof
sketch: induction over the triggers; a trigger is not in the table namespace
({name}`Catalog.findTable_createTrigger`). -/
theorem Database.findTable_appendTriggers (database : Database) (triggers : List (Identifier × CatalogTrigger))
    (name : Identifier) :
    (triggers.foldl (fun database trigger => database.appendTrigger trigger.1 trigger.2) database).catalog.findTable
      name = database.catalog.findTable name := by
  induction triggers generalizing database with
  | nil => rfl
  | cons trigger rest ih =>
    rw [List.foldl_cons, ih]
    exact Catalog.findTable_createTrigger _ _ _ _

/-- For every database whose catalog finds the table by name at a position, the migration's catalog finds the
same position with the shape of {name}`Table.addDerivedColumn`. Proof sketch: the triggers do not change a
table lookup ({name}`Database.findTable_appendTriggers`), and {name}`Catalog.findTable_addColumn` gives the
lookup after the column is added; the table at the position exists ({name}`Catalog.tableAt_of_findTable`). -/
theorem Database.findTable_addDerivedColumn {database : Database} {tableName : Identifier} {position : Nat}
    {table : Table} (column : CatalogColumn) (derived : Resolved.Expr)
    (triggers : List (Identifier × CatalogTrigger))
    (found : database.catalog.findTable tableName = some (position, table.shape)) :
    (database.addDerivedColumn position table column derived triggers).catalog.findTable tableName =
      some (position, (table.addDerivedColumn column derived).shape) := by
  rw [Database.addDerivedColumn, Database.findTable_appendTriggers]
  simp only [Database.setRows, Database.addColumn]
  rw [Catalog.findTable_addColumn, found, Option.map_some]
  simp [Catalog.tableAt_of_findTable found, Table.addDerivedColumn]

/-- For every database whose catalog finds the table by name at an aligned position where the database has the
table, the migration keeps the number of stored rows of the table, whatever column, expression and triggers it
adds. In plain words: adding a derived column and its triggers does not add or remove a row. Proof sketch:
the stored rows at the position are those of {name}`Table.addDerivedColumn` ({name}`Database.table_addDerivedColumn`),
which maps each row to one row. -/
theorem Database.rows_length_addDerivedColumn {database : Database} {tableName : Identifier} {position : Nat}
    {table : Table} (column : CatalogColumn) (derived : Resolved.Expr)
    (triggers : List (Identifier × CatalogTrigger))
    (found : database.catalog.findTable tableName = some (position, table.shape))
    (present : database.table position = some table) (aligned : position < database.rows.length) :
    ((database.addDerivedColumn position table column derived triggers).rows.getD position []).length =
      (database.rows.getD position []).length := by
  have oldRows : table.rows = database.rows.getD position [] := by
    have := Database.table_of_findTable database _ position table.shape found
    rw [present] at this
    exact congrArg Table.rows (Option.some.inj this)
  have newTable := Database.table_of_findTable (database.addDerivedColumn position table column derived triggers) _
    position _ (Database.findTable_addDerivedColumn column derived triggers found)
  rw [Database.table_addDerivedColumn column derived triggers present aligned] at newTable
  have stored := congrArg Table.rows (Option.some.inj newTable)
  dsimp only at stored
  rw [← stored]
  simp [Table.addDerivedColumn, oldRows]

/-- For every original table with wide aliased rows, in-range primary-key positions, no generated column,
appended column without a generated expression, and expression that reads only the old columns, evaluated in
the plain context without parameters ({name}`EvalContext.plain` with clock 0), the scan of {name}`Table.addDerivedColumn` is the scan of the original with the stored value of the
expression appended to each row. The row order, the rowids and the key order of the original table decide
the order, whatever the stored order. Proof sketch: the actual backfill UPDATE computes these rows
({name}`updated_derived_append`), and {name}`sourceRows_updated_derived` transports the scan. -/
theorem sourceRows_addDerivedColumn (table : Table) (column : CatalogColumn) (derived : Resolved.Expr)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (below : derived.readsBelow table.shape.columns.length = true)
    (keysInside : ∀ position ∈ table.shape.primaryKey, position < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none) (newPlain : column.generated = none) :
    sourceRows (table.addDerivedColumn column derived) =
      (sourceRows table).map fun cells =>
        cells ++ [Value.store column.affinity (derived.eval (EvalContext.plain 0) cells)] := by
  have rows := updated_derived_append (EvalContext.plain 0) (EvalContext.plain_rowFree 0) table column derived
    wide aliased below plain newPlain
  have equal : LiteralData.updated (EvalContext.plain 0) (table.appendColumns [(column, .null)])
      [(table.shape.columns.length, derived)] none = table.addDerivedColumn column derived :=
    congrArg (fun rows : List Row => ({ shape := (table.addDerivedColumn column derived).shape, rows } : Table)) rows
  rw [← equal]
  exact sourceRows_updated_derived (EvalContext.plain 0) (EvalContext.plain_rowFree 0) table column derived wide
    aliased below keysInside plain newPlain

end Belay.Sqlite.Model
