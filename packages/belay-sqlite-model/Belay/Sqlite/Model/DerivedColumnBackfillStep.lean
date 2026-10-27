import Belay.Sqlite.Model.BackfillStatementResolution
import Belay.Sqlite.Model.DerivedColumnTable
import Belay.Sqlite.Model.ScriptStepDatabase

set_option doc.verso true

/-! The backfill step of a migration (ADR 0017, S6): the connection that a successful step of
{lit}`UPDATE t SET c = e` reaches, where {lit}`c` is the column that ADD COLUMN just appended. The theorem
combines the resolution of the statement, the actual effect of the plain UPDATE and the row law of the
backfill, without assuming that the rows have a desired form. -/

namespace Belay.Sqlite.Model
open Resolved

/-- For every connection whose named table is an original table with an appended column that holds NULL in
every row, and every error-free step of {lit}`UPDATE t SET name = value` that continues: if the written
value resolves to an expression of the old columns, and the resolved assignment is context-free
({name}`Resolved.Expr.ContextFree`), the next connection is the connection with the rows of the table
replaced by those of {name}`Table.addDerivedColumn` and some counters. Clock, snapshot and both settings
stay. The original rows must be wide and aliased, the original columns and the appended column must have no
generated expression, and the name must resolve to the appended column. Both settings are off, and the
exact UPDATE event fires no trigger in the extended catalog. The expression, the table shape and the
other tables and triggers are arbitrary otherwise. Proof sketch: the statement resolves to the plain
UPDATE of the assignment ({name}`backfill_resolution`); the actual effect stores the rows of
{name}`LiteralData.updated` ({name}`plainUpdate_database`); {name}`updated_derived_append` computes them
and context-freeness moves the evaluation to the canonical context. -/
theorem backfill_step {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {tableName name : Identifier} {value : Syntax.Expr} {position : Nat} (table : Table)
    (column : CatalogColumn) {derived : Resolved.Expr} {affinity : Option Affinity}
    (found : connection.state.database.catalog.findTable tableName = some (position,
      { table.shape with columns := table.shape.columns ++ [column] }))
    (present : connection.state.database.table position = some (table.appendColumns [(column, .null)]))
    (added : columnPosition (table.shape.columns ++ [column]) name = some table.shape.columns.length)
    (newPlain : column.generated = none)
    (operand : resolveOperand context.profile.dqsDml (backfillScope position tableName table.shape column) {} true
      value = .ok (derived, affinity))
    (below : derived.readsBelow table.shape.columns.length = true)
    (contextFree : (assignedExpression (backfillScope position tableName table.shape column)
      table.shape.columns.length value derived).ContextFree)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none)
    (foreign : connection.foreignKeys = false) (recursive : connection.recursiveTriggers = false)
    (noneFiring : connection.state.database.catalog.triggersFiring
      { table := position, event := .update (some [table.shape.columns.length]) } = [])
    (step : runScriptStep context clock index connection (.update tableName [(name, value)] none [] [])
      parameters = .continued output next others)
    (noError : output.isError = false) :
    ∃ counters, next = { connection with state := { connection.state with
      database := connection.state.database.setRows position
        (table.addDerivedColumn column (assignedExpression
          (backfillScope position tableName table.shape column) table.shape.columns.length value derived)).rows,
      counters } } := by
  obtain ⟨resolved, after, -, resolution, -⟩ := runScriptStep_ran step
  obtain ⟨rfl, rfl⟩ := backfill_resolution (state := connection.resolveState) (tableName := tableName)
    (table := table.shape) found added newPlain operand foreign recursive noneFiring resolution
  obtain ⟨_, -, stored⟩ := plainUpdate_database resolution present step noError
  have assignedBelow := assignedExpression_readsBelow (scope := backfillScope position tableName table.shape column)
    (position := table.shape.columns.length) (expression := value) below
  rw [updated_derived_append _ (statementContext_nil_rowFree _ _ _ _) table column _ wide aliased assignedBelow plain
    newPlain] at stored
  refine runScriptStep_next_of_database resolution rfl step noError ?_
  rw [stored]
  congr 1
  simp only [Table.addDerivedColumn]
  exact congrArg (fun rows : List Row => rows) (List.map_congr_left fun row _ => by rw [contextFree])

end Belay.Sqlite.Model
