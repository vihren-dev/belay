import Belay.Sqlite.Model.Programs.Scripts.CatalogChangeRules
import Belay.Sqlite.Model.Programs.Scripts.AddColumnRule
import Belay.Sqlite.Model.Programs.Scripts.SuccessfulScriptEffects
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
sketch: {name}`addColumn_resolution_cases` identifies the prepare error or the addition.
{name}`runScriptStep_prepareError_eq` contradicts the successful output in the first case.
{name}`runScriptStep_addColumn_eq` gives the next connection in the second, since a column
without constraints reads a NULL default. -/
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
    · rw [runScriptStep_prepareError_eq resolution] at step
      cases step; cases noError
    · have quiet : (definedColumn table.shape.strict definition).clockDefault = false := by
        simp [definedColumn, CatalogColumn.clockDefault]
      have read : readDefaultValue (definedColumn table.shape.strict definition) = .ok .null := rfl
      rw [runScriptStep_addColumn_eq resolution] at step
      simp only [quiet, read, present, Except.toOption, Option.isSome_some, Bool.or_true, ite_true, Bool.false_eq_true, ite_false] at step
      repeat' split at step
      all_goals cases step
      all_goals first | contradiction | exact ⟨_, rfl⟩

end Belay.Sqlite.Model
