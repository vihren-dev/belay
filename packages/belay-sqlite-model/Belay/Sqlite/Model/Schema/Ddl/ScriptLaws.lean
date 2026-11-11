import Belay.Sqlite.Model.Schema.Columns.SqlLaws
import Belay.Sqlite.Model.Schema.Dispatch.StatementStep

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every clock value, counters, list of values, database, name and table: when the catalog position is the end
of the catalog and the database has one row list for each catalog object, CREATE TABLE
succeeds with the table added to the catalog ({name}`Catalog.createTable`) and no rows.
Proof sketch: {name}`literalStep` is {name}`step` here, whose position check holds. -/
theorem effect_createTable_ok (clock : Int) (counters : Counters) (parameters : List Value) (database : Database) (name : Identifier) (table : CatalogTable)
    (target : Nat) (atEnd : target = database.catalog.length) (rows : database.rows.length = database.catalog.length) :
    literalStep clock counters parameters (.createTable target name table) database =
      .ok { catalog := database.catalog.createTable name table, rows := database.rows ++ [[]] } := by
  subst atEnd
  simp [literalStep, runStatement, step, rows]

/-- For every clock value, counters, list of values, database, position, table, column and value: when the table is
at the position, the column has no time default, its default reads as the value
({name}`readDefaultValue`), the column is not NOT NULL with a NULL value over rows, and
every row with the value appended satisfies the column's CHECK constraints
({name}`LiteralData.checkHolds`), ADD COLUMN succeeds with the column appended and the
value in every row ({name}`Database.addColumn`). Proof sketch: {name}`literalStep` is
{name}`step` here, and the premises select its successful branch. -/
theorem effect_addColumn_ok (clock : Int) (counters : Counters) (parameters : List Value) {database : Database} {target : Nat} {table : Table}
    {column : CatalogColumn} {value : Value} (present : database.table target = some table)
    (constant : column.clockDefault = false) (read : readDefaultValue column = .ok value)
    (allowed : (column.notNull && value == .null && !table.rows.isEmpty) = false)
    (checked : table.rows.all (fun row => column.checks.all
      (LiteralData.checkHolds { row with values := row.values ++ [value] })) = true) :
    literalStep clock counters parameters (.addColumn target column) database = .ok (database.addColumn target column value) := by
  simp [literalStep, runStatement, step, present, constant, read, allowed, checked]

/-- For every clock value, counters, list of values, database, position, table, rows and {lit}`RETURNING`
columns of an INSERT without subqueries: when the table is at the position, no row at the clock
value with the values ({name}`Resolved.rowsAt` in the plain context of the clock value with the counters and the
values as its parameters) has
a rowid alias that SQLite refuses ({name}`LiteralData.aliasMismatch`), and the table with
the rows inserted ({name}`LiteralData.inserted`) meets {name}`LiteralData.constraints` (its
NOT NULL cells and its unique keys) and has distinct rowids, INSERT succeeds with the
table's rows replaced by those rows ({name}`Database.setRows`). Proof sketch: the
premises select the successful branches of {name}`insertOutcome` and
{name}`checkedWrite`. -/
theorem effect_write_ok (clock : Int) (counters : Counters) (parameters : List Value) {database : Database} {target : Nat} {table : Table}
    {rows : List (List Resolved.Cell)} {returning : List (Resolved.Expr × String)}
    (present : database.table target = some table)
    (aligned : (Resolved.rowsAt { Resolved.EvalContext.plain clock with parameters, counters } table.shape.columns rows).findIdx? (LiteralData.aliasMismatch table.shape) = none)
    (checked : (LiteralData.constraints (database.keys target table)
        (LiteralData.inserted table (Resolved.rowsAt { Resolved.EvalContext.plain clock with parameters, counters } table.shape.columns rows)) &&
      LiteralData.rowidsDistinct (LiteralData.inserted table (Resolved.rowsAt { Resolved.EvalContext.plain clock with parameters, counters } table.shape.columns rows))) = true) :
    literalStep clock counters parameters (.insert target rows returning) database =
      .ok (database.setRows target (LiteralData.inserted table (Resolved.rowsAt { Resolved.EvalContext.plain clock with parameters, counters } table.shape.columns rows)).rows) := by
  simp only [literalStep, runStatement, Resolved.statementContext_nil, present, insertOutcome, aligned, checkedWrite,
    checked, ite_true, StatementRun.withKeys, Option.map]

end Belay.Sqlite.Model
