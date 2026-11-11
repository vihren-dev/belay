import Belay.Sqlite.Model.Programs.StatementRunLaws.AddColumnEffect
import Belay.Sqlite.Model.Programs.Scripts.ScriptStepDatabase
import Belay.Sqlite.Model.Schema.Columns.AddColumnPlainStep

set_option doc.verso true

/-! ADD COLUMN of a column with no constraint (ADR 0017, S6). The written column has a name and
perhaps a declared type, and no DEFAULT, NOT NULL, CHECK, REFERENCES or other constraint. SQLite fills
its existing rows with NULL, and the statement needs no column check. The module gives the resolution
of such a statement and the connection that a successful step reaches. -/

namespace Belay.Sqlite.Model

/-- For every connection, table name, column definition without constraints, table at the catalog
position of the name, and error-free step of ADD COLUMN that continues: if the table's strictness
admits the declared type, the next connection is the connection with the database in which the table
has {name}`definedColumn` appended and NULL appended to every row, with some counters. In plain words, a
column without a default starts as NULL in every row, and clock, snapshot and settings stay. Proof
sketch: resolution gives the addition ({name}`addColumn_resolution_cases`); a prepare error is excluded by
the error-free output; {name}`addColumn_database` gives the stored database, in which the default of a
column without one reads as NULL; {name}`runScriptStep_next_of_database` gives the connection. -/
theorem addColumn_plain_step {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {tableName : Identifier} {definition : Syntax.ColumnDefinition} {position : Nat} {table : Table}
    (plain : definition.constraints = [])
    (admitted : addColumnRestriction table.shape definition = none)
    (found : connection.state.database.catalog.findTable tableName = some (position, table.shape))
    (present : connection.state.database.table position = some table)
    (step : runScriptStep context clock index connection (.addColumn tableName definition) parameters =
      .continued output next others)
    (noError : output.isError = false) :
    ∃ counters, next = { connection with state := { connection.state with
      database := connection.state.database.addColumn position (definedColumn table.shape.strict definition) .null,
      counters } } := by
  obtain ⟨resolved, after, -, resolution, -⟩ := runScriptStep_ran step
  have body := resolution
  simp only [statement_arms, ResolveState.withCatalog, Except.map] at body
  split at body
  · cases body
  · rename_i pair bodyOk
    obtain ⟨resolvedBody, catalog⟩ := pair
    cases body
    rcases addColumn_resolution_cases plain admitted found bodyOk with ⟨error, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨value, database, -, effect, -⟩ := runScriptStep_effect resolution rfl step noError
      simp [SqlState.statementRun, runStatement, Belay.Sqlite.Model.step] at effect
    · obtain ⟨cell, clockNull, clockRead, stored⟩ := addColumn_database resolution present step noError
      have noClock : (definedColumn table.shape.strict definition).clockDefault = false := by
        simp [definedColumn, CatalogColumn.clockDefault]
      have same : cell = .null := by
        have read : readDefaultValue (definedColumn table.shape.strict definition) = .ok .null := rfl
        rw [clockRead noClock] at read
        exact Except.ok.inj read
      rw [same] at stored
      exact runScriptStep_next_of_database resolution rfl step noError stored

end Belay.Sqlite.Model
