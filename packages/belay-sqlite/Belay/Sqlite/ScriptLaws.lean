import Belay.Sqlite.SqlLaws
import Belay.Sqlite.Resolution.StatementCatalog

set_option doc.verso true

/-! The lemmas with which a proof computes a script (ADR 0013, D8): one statement at a
time ({lit}`runSqlFrom_cons`, {lit}`advance_effect`), the effects of the statements that
succeed ({lit}`effect_createTable_ok`, {lit}`effect_addColumn_ok`, {lit}`effect_write_ok`),
and {lit}`SqlState.publish_ok` for the next state. A proof that uses them does not unfold
{lit}`runSql`, {lit}`runSqlFrom`, {lit}`advance`, {lit}`literalStep` or {lit}`step`. The
frame lemmas of the database, for example {lit}`Database.table_setRows_other` (a write
to position {lit}`k` leaves every other position as it was), are in
{lit}`DatabaseLaws.lean`. -/

namespace Belay.Sqlite

/-- For every script and database, {name}`runSql` runs the script from position zero in
the idle state of the database. -/
theorem runSql_eq (script : List Resolved.Statement) (database : Database) :
    runSql script database = runSqlFrom 0 script { database := database } := rfl

/-- For every position and state, the run of no statement finishes the state with its
database ({name}`SqlState.finish`). -/
@[simp] theorem runSqlFrom_nil (position : Nat) (state : SqlState) :
    runSqlFrom position [] state = state.finish (.success state.database) := rfl

/-- For every position, statement, rest of the script and state, the run advances the
first statement ({name}`advance`): a halt is the outcome, and a next state runs the
rest from the next position. -/
theorem runSqlFrom_cons (position : Nat) (statement : Resolved.Statement) (rest : List Resolved.Statement)
    (state : SqlState) :
    runSqlFrom position (statement :: rest) state = match advance position statement state with
      | .halt outcome => outcome
      | .next next => runSqlFrom (position + 1) rest next := rfl

/-- For every position, state and statement that is not transaction control
({name}`Resolved.Statement.isControl`), {name}`advance` publishes the statement's effect
({name}`literalStep`) at the clock value of the position ({name}`SqlState.publish`). -/
theorem advance_effect (position : Nat) (statement : Resolved.Statement) (state : SqlState)
    (ordinary : statement.isControl = false) :
    advance position statement state = state.publish position (literalStep (state.clock position) statement state.database) := by
  cases statement <;> simp_all [advance, Resolved.Statement.isControl]

/-- For every position, state and CREATE TABLE, {name}`advance` publishes its effect
({name}`advance_effect` for this form, which {lit}`simp` can use without a side goal). -/
@[simp] theorem advance_createTable (step : Nat) (state : SqlState) (target : Nat) (name : String) (table : CatalogTable) :
    advance step (.createTable target name table) state = state.publish step (literalStep (state.clock step) (.createTable target name table) state.database) := rfl

/-- For every position, state and CREATE INDEX, {name}`advance` publishes its effect
({name}`advance_effect` for this form, which {lit}`simp` can use without a side goal). -/
@[simp] theorem advance_createIndex (step : Nat) (state : SqlState) (target : Nat) (name : String) (index : CatalogIndex) :
    advance step (.createIndex target name index) state = state.publish step (literalStep (state.clock step) (.createIndex target name index) state.database) := rfl

/-- For every position, state and ADD COLUMN, {name}`advance` publishes its effect
({name}`advance_effect` for this form, which {lit}`simp` can use without a side goal). -/
@[simp] theorem advance_addColumn (step : Nat) (state : SqlState) (target : Nat) (column : CatalogColumn) :
    advance step (.addColumn target column) state = state.publish step (literalStep (state.clock step) (.addColumn target column) state.database) := rfl

/-- For every position, state and INSERT, {name}`advance` publishes its effect
({name}`advance_effect` for this form, which {lit}`simp` can use without a side goal). -/
@[simp] theorem advance_insert (step : Nat) (state : SqlState) (target : Nat) (rows : List (List Resolved.Cell)) (returning : List (Resolved.Expr × String)) :
    advance step (.insert target rows returning) state = state.publish step (literalStep (state.clock step) (.insert target rows returning) state.database) := rfl

/-- For every position, state and INSERT with clauses or an algorithm, {name}`advance` publishes its effect
({name}`advance_effect` for this form, which {lit}`simp` can use without a side goal). -/
@[simp] theorem advance_upsert (step : Nat) (state : SqlState) (target : Nat) (rows : List (List Resolved.Cell)) (clauses : List Resolved.ConflictClause)
    (returning : List (Resolved.Expr × String)) (algorithm : Option ConflictAlgorithm) :
    advance step (.upsert target rows clauses returning algorithm) state = state.publish step (literalStep (state.clock step) (.upsert target rows clauses returning algorithm) state.database) := rfl

/-- For every position, state and UPDATE, {name}`advance` publishes its effect
({name}`advance_effect` for this form, which {lit}`simp` can use without a side goal). -/
@[simp] theorem advance_update (step : Nat) (state : SqlState) (target : Nat) (assignments : List (Nat × Resolved.Expr)) (filter : Option Resolved.Expr)
    (returning : List (Resolved.Expr × String)) :
    advance step (.update target assignments filter returning) state = state.publish step (literalStep (state.clock step) (.update target assignments filter returning) state.database) := rfl

/-- For every position, state and DELETE, {name}`advance` publishes its effect
({name}`advance_effect` for this form, which {lit}`simp` can use without a side goal). -/
@[simp] theorem advance_delete (step : Nat) (state : SqlState) (target : Nat) (filter : Option Resolved.Expr) (returning : List (Resolved.Expr × String)) :
    advance step (.delete target filter returning) state = state.publish step (literalStep (state.clock step) (.delete target filter returning) state.database) := rfl

/-- For every position, state and a query, {name}`advance` publishes its effect
({name}`advance_effect` for this form, which {lit}`simp` can use without a side goal). -/
@[simp] theorem advance_query (step : Nat) (state : SqlState) (query : Resolved.Query) :
    advance step (.query query) state = state.publish step (literalStep (state.clock step) (.query query) state.database) := rfl

/-- For every position, state and a statement that SQLite refuses, {name}`advance` publishes its effect
({name}`advance_effect` for this form, which {lit}`simp` can use without a side goal). -/
@[simp] theorem advance_prepareError (step : Nat) (state : SqlState) (error : PrepareError) :
    advance step (.prepareError error) state = state.publish step (literalStep (state.clock step) (.prepareError error) state.database) := rfl

/-- For every state, position and database, publishing an effect that succeeds with the
database continues with the state that has that database. -/
@[simp] theorem SqlState.publish_ok (state : SqlState) (position : Nat) (database : Database) :
    state.publish position (.ok database) = .next { state with database } := rfl

/-- For every idle database, position, reason other than FAIL and reached database,
publishing an effect that fails halts with the failure at the position over the idle
database: an idle state keeps its database for every error but FAIL. -/
theorem SqlState.publish_error_idle (database : Database) (position : Nat) (reason : ExecutionError)
    (reached : Database) (notFail : reason ≠ .constraintFail) :
    ({ database := database } : SqlState).publish position (.error (reason, reached)) =
      .halt (.failure position reason database) := by
  simp [SqlState.publish, notFail, SqlState.failed_idle]

/-- For every idle database, position, prepare error and reached database, publishing
the prepare error halts with the failure at the position over the idle database
({name}`SqlState.publish_error_idle` for this error, which {lit}`simp` can use without a
side goal). -/
@[simp] theorem SqlState.publish_prepare_idle (database : Database) (position : Nat) (error : PrepareError)
    (reached : Database) :
    ({ database := database } : SqlState).publish position (.error (.prepare error, reached)) =
      .halt (.failure position (.prepare error) database) :=
  SqlState.publish_error_idle database position _ reached (by simp)

/-- For every clock value, database and prepare error, the effect of the statement that
SQLite refuses to prepare is that error over the database. -/
@[simp] theorem effect_prepareError (clock : Int) (database : Database) (error : PrepareError) :
    literalStep clock (.prepareError error) database = .error (.prepare error, database) := rfl

/-- For every clock value, database, name and table: when the catalog position is the end
of the catalog and the database has one row list for each catalog object, CREATE TABLE
succeeds with the table added to the catalog ({name}`Catalog.createTable`) and no rows. -/
theorem effect_createTable_ok (clock : Int) (database : Database) (name : String) (table : CatalogTable)
    (target : Nat) (atEnd : target = database.catalog.length) (rows : database.rows.length = database.catalog.length) :
    literalStep clock (.createTable target name table) database =
      .ok { catalog := database.catalog.createTable name table, rows := database.rows ++ [[]] } := by
  subst atEnd
  simp [literalStep, step, rows]

/-- For every clock value, database, position, table, column and value: when the table is
at the position, the column has no time default, its default reads as the value
({name}`readDefaultValue`), and the column is not NOT NULL with a NULL value over rows,
ADD COLUMN succeeds with the column appended and the value in every row
({name}`Database.addColumn`). -/
theorem effect_addColumn_ok (clock : Int) {database : Database} {target : Nat} {table : Table}
    {column : CatalogColumn} {value : Value} (present : database.table target = some table)
    (constant : column.clockDefault = false) (read : readDefaultValue column = .ok value)
    (allowed : (column.notNull && value == .null && !table.rows.isEmpty) = false) :
    literalStep clock (.addColumn target column) database = .ok (database.addColumn target column value) := by
  simp [literalStep, step, present, constant, read, allowed]

/-- For every clock value, database, position, table, rows and {lit}`RETURNING` columns:
when the table is at the position, no row at the clock value ({name}`Resolved.rowsAt`) has
a rowid alias that SQLite refuses ({name}`LiteralData.aliasMismatch`), and the table with
the rows inserted ({name}`LiteralData.inserted`) keeps its unique keys and distinct rowids,
INSERT succeeds with the table's rows replaced by those rows ({name}`Database.setRows`). -/
theorem effect_write_ok (clock : Int) {database : Database} {target : Nat} {table : Table}
    {rows : List (List Resolved.Cell)} {returning : List (Resolved.Expr × String)}
    (present : database.table target = some table)
    (aligned : (Resolved.rowsAt clock table.shape.columns rows).findIdx? (LiteralData.aliasMismatch table.shape) = none)
    (checked : (LiteralData.constraints (database.keys target table)
        (LiteralData.inserted table (Resolved.rowsAt clock table.shape.columns rows)) &&
      LiteralData.rowidsDistinct (LiteralData.inserted table (Resolved.rowsAt clock table.shape.columns rows))) = true) :
    literalStep clock (.insert target rows returning) database =
      .ok (database.setRows target (LiteralData.inserted table (Resolved.rowsAt clock table.shape.columns rows)).rows) := by
  simp only [literalStep, present, insertOutcome, aligned, checkedWrite, checked, ite_true]

end Belay.Sqlite
