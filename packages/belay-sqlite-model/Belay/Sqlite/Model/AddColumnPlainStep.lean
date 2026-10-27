import Belay.Sqlite.Model.AddColumnEffect
import Belay.Sqlite.Model.ScriptStepDatabase
import Belay.Sqlite.Model.CatalogAddColumnSearch
import Belay.Sqlite.Model.ExprResolutionLaws

set_option doc.verso true

/-! ADD COLUMN of a column with no constraint (ADR 0017, S6). The written column has a name and
perhaps a declared type, and no DEFAULT, NOT NULL, CHECK, REFERENCES or other constraint. SQLite fills
its existing rows with NULL, and the statement needs no column check. The module gives the resolution
of such a statement and the connection that a successful step reaches. -/

namespace Belay.Sqlite.Model

/-- For every resolution context, catalog, table name, table at a catalog position and column definition without
constraints: if the table's strictness admits the declared type ({name}`addColumnRestriction`), then a
successful resolution of ADD COLUMN gives a prepare error with the catalog unchanged, or the addition of
{name}`definedColumn` at the position of the table with the catalog that holds the column. A model
restriction cannot satisfy the success premise. The column has no {lit}`REFERENCES`, so the statement
does not refuse a populated table, whatever {lit}`enforced` is. Proof sketch: reduce the empty
constraint list, then split the remaining name and width checks. -/
theorem addColumn_resolution_cases {context : ResolveContext} {enforced : Bool} {catalog : Catalog}
    {tableName : Identifier} {definition : Syntax.ColumnDefinition} {position : Nat} {table : CatalogTable}
    {resolved : Resolved.Statement} {next : Catalog}
    (plain : definition.constraints = [])
    (admitted : addColumnRestriction table definition = none)
    (found : catalog.findTable tableName = some (position, table))
    (ok : resolveAddColumn context catalog enforced tableName definition = .ok (resolved, next)) :
    (∃ error, resolved = .prepareError error ∧ next = catalog) ∨
      (resolved = .addColumn position (definedColumn table.strict definition) false ∧
        next = catalog.addColumn position (definedColumn table.strict definition)) := by
  have metadata : addedColumn table.strict definition = some (definedColumn table.strict definition) := by
    simp [addedColumn, plain]
  have read : readDefaultValue (definedColumn table.strict definition) = .ok .null := rfl
  have fits : strictDefaultFits (definedColumn table.strict definition) = true := by
    unfold strictDefaultFits
    rw [read]
    cases (definedColumn table.strict definition).strictType with
    | none => rfl
    | some strictType => cases strictType <;> rfl
  simp only [resolveAddColumn, found] at ok
  simp only [plain, admitted, metadata, fits] at ok
  simp only [plain, List.findSome?_nil, List.any_nil, Bool.false_and,
    Bool.false_eq_true, Bool.not_true, ↓reduceIte, columnChecks, List.zipIdx_nil,
    List.filterMapM_nil, addedForeignKeys, List.foldl_nil, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact .inl ⟨_, rfl, rfl⟩)
    | (cases ok; exact .inr ⟨by simp [definedColumn], rfl⟩)
    | cases ok

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
