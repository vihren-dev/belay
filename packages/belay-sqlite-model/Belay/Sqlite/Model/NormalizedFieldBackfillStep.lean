import Belay.Sqlite.Model.NormalizedFieldUpdateResolution
import Belay.Sqlite.Model.NormalizedFieldEffects
import Belay.Sqlite.Model.SuccessfulScriptEffects

set_option doc.verso true

/-! The actual backfill step of the lowercase-field expansion. Its resolution,
its successful effect and the row map are combined into the exact reached
connection, without assuming a desired row relation. -/

namespace Belay.Sqlite.Model.NormalizedField
open Resolved

/-- The stored rows after the backfill: each original row of the table with the
lowercase of its source cell appended. This is the row map that the actual UPDATE
effect is proved to store; it is not an assumption on any database. -/
def loweredRows (table : Table) (source : Nat) : List Row :=
  table.rows.map fun row => row.appendValues [mapText lowerByte (row.values.getD source .null)]

/-- For every connection whose named table is the original table with the plain
TEXT field appended (NULL in every row), and every continuing error-free backfill
step, the reached connection is the same connection with the target's rows
replaced by {name}`loweredRows` and some counters. Clock, snapshot and both
settings are unchanged. The original rows must be wide and aliased, and the
original columns must have no generated expression. The hypotheses name the
extended catalog entry, the foreign-key and recursive-trigger settings and the
exact empty trigger selection. Proof sketch: the resolution is the plain
assignment; its actual effect stores the computed rows; the row-map law
identifies them. -/
theorem backfill_step {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {parameters : List Value} {output : Output}
    {tableName name sourceName : Identifier} {position source : Nat} (table : Table)
    (found : connection.state.database.catalog.findTable tableName = some (position,
      { table.shape with columns := table.shape.columns ++ [textColumn name table.shape.strict] }))
    (present : connection.state.database.table position =
      some (table.appendColumns [(textColumn name table.shape.strict, .null)]))
    (fresh : columnPosition table.shape.columns name = none)
    (sourceFound : columnPosition table.shape.columns sourceName = some source)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none)
    (foreign : connection.foreignKeys = false) (recursive : connection.recursiveTriggers = false)
    (noneFiring : connection.state.database.catalog.triggersFiring
      { table := position, event := .update (some [table.shape.columns.length]) } = [])
    (step : runScriptStep context clock index connection
      (.update tableName [(name, .call "lower" [.identifier sourceName .none])] none [] [])
      parameters = .continued output next)
    (noError : output.isError = false) :
    ∃ counters, next = { connection with state := { connection.state with
      database := connection.state.database.setRows position (loweredRows table source), counters } } := by
  obtain ⟨resolved, after, _, resolution, _⟩ := runScriptStep_ran step
  obtain ⟨rfl, rfl⟩ := backfill_resolution (state := connection.resolveState)
    (tableName := tableName) found fresh sourceFound foreign recursive noneFiring resolution
  obtain ⟨value, database, _, effect, advanced⟩ := runScriptStep_effect resolution rfl step noError
  have inside : source < table.shape.columns.length := by
    obtain ⟨pair, located, equal⟩ := Option.map_eq_some_iff.mp sourceFound
    subst equal
    exact (List.getElem?_eq_some_iff.mp ((findPosition_eq_some_iff _ _ _ _).mp located).1).1
  have stored := runStatement_update_ok value _ parameters
    (database := connection.state.database) (target := position) _ none [] [] present
    (by simpa [SqlState.statementRun] using effect)
  have text : (textColumn name table.shape.strict).affinity = .text := by cases table.shape.strict <;> rfl
  rw [updated_lower_append _ table _ source wide aliased inside plain rfl text] at stored
  subst stored
  exact ⟨_, advanced⟩

end Belay.Sqlite.Model.NormalizedField
