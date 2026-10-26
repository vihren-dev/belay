import Belay.Sqlite.Model.NormalizedFieldResolution
import Belay.Sqlite.Model.SuccessfulScriptEffects
import Belay.Sqlite.Model.ScriptLaws

set_option doc.verso true

/-! The successful ADD COLUMN and trigger-registration steps surrounding the
backfill. Their effects come from actual script steps, including resolution
and support checks; no trigger body is executed during registration. -/

namespace Belay.Sqlite.Model.NormalizedField

/-- A successful public-style step that adds the plain TEXT field to the named
physical table appends NULL to its rows. The reached connection is the same one
with that database and some counters; clock, snapshot and both settings are
unchanged. The supplied output must be error-free; merely continuing after an
SQL error would not suffice. Proof sketch: resolution either chooses the exact addition
or a prepare error; success excludes the latter and the actual effect gives
the database operation. -/
theorem add_step {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {tableName name : Identifier} {position : Nat} {table : Table}
    (found : connection.state.database.catalog.findTable tableName = some (position, table.shape))
    (present : connection.state.database.table position = some table)
    (step : runScriptStep context clock index connection
      (.addColumn tableName (textDefinition name)) parameters = .continued output next others)
    (noError : output.isError = false) :
    ∃ counters, next = { connection with state := { connection.state with
      database := connection.state.database.addColumn position (textColumn name table.shape.strict) .null,
      counters } } := by
  obtain ⟨resolved, after, _, resolution, _⟩ := runScriptStep_ran step
  have body := resolution
  simp only [statement_arms, ResolveState.withCatalog, Except.map] at body
  split at body
  · cases body
  · rename_i pair bodyOk
    obtain ⟨resolvedBody, catalog⟩ := pair
    cases body
    rcases addColumn_resolution_cases found bodyOk with ⟨error, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨value, database, _, effect, _⟩ := runScriptStep_effect resolution rfl step noError
      simp [SqlState.statementRun, runStatement, Belay.Sqlite.Model.step] at effect
    · obtain ⟨value, database, _, effect, advanced⟩ := runScriptStep_effect resolution rfl step noError
      have added : (connection.state.statementRun value parameters
          (.addColumn position (textColumn name table.shape.strict))).effect =
          .ok (connection.state.database.addColumn position (textColumn name table.shape.strict) .null) := by
        apply effect_addColumn_ok value {} parameters present
        · rfl
        · rfl
        · rfl
        · simp [textColumn]
      rw [added] at effect
      cases effect
      exact ⟨_, advanced⟩

/-- CREATE TRIGGER without IF NOT EXISTS either resolves to a prepare error or
appends exactly its written trigger. No body executes in either resolution
case. Proof sketch: split the existing resolver's preparation checks. -/
private theorem trigger_resolution_cases {catalog next : Catalog} {name : Identifier}
    {trigger : CatalogTrigger} {resolved : Resolved.Statement}
    (ok : resolveCreateTrigger catalog name false trigger = .ok (resolved, next)) :
    (∃ error, resolved = .prepareError error ∧ next = catalog) ∨
      (resolved = .createTrigger catalog.length name trigger ∧ next = catalog.createTrigger name trigger) := by
  unfold resolveCreateTrigger at ok
  simp only [prepareError, Bool.false_eq_true, ↓reduceIte] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact .inl ⟨_, rfl, rfl⟩)
    | (cases ok; exact .inr ⟨rfl, rfl⟩)
    | cases ok

/-- A successful actual CREATE TRIGGER step appends that catalog object and an
empty storage slot, leaving prior table rows unchanged. The reached connection
is the same one with that database and some counters; clock, snapshot and both
settings are unchanged. The
trigger may have any admitted written body; registration does not execute it.
Proof sketch: success excludes preparation errors and the executor's storage
alignment failure, leaving its single append effect. -/
theorem trigger_step {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {parameters : List Value} {output : Output} {others : List StatementExecution}
    (name : Identifier) (trigger : CatalogTrigger)
    (step : runScriptStep context clock index connection
      (.createTrigger name false trigger.time trigger.event trigger.table trigger.condition trigger.body)
      parameters = .continued output next others)
    (noError : output.isError = false) :
    ∃ counters, next = { connection with state := { connection.state with
      database := { catalog := connection.state.database.catalog.createTrigger name trigger,
                    rows := connection.state.database.rows ++ [[]] },
      counters } } := by
  obtain ⟨resolved, after, _, resolution, _⟩ := runScriptStep_ran step
  have body := resolution
  simp only [statement_arms, ResolveState.withCatalog, Except.map] at body
  split at body
  · cases body
  · rename_i pair bodyOk
    obtain ⟨resolvedBody, catalog⟩ := pair
    cases body
    rcases trigger_resolution_cases bodyOk with ⟨error, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨value, database, _, effect, _⟩ := runScriptStep_effect resolution rfl step noError
      simp [SqlState.statementRun, runStatement, Belay.Sqlite.Model.step] at effect
    · obtain ⟨value, database, _, effect, advanced⟩ := runScriptStep_effect resolution rfl step noError
      simp only [SqlState.statementRun, runStatement, Belay.Sqlite.Model.step] at effect
      split at effect
      · cases effect
        exact ⟨_, advanced⟩
      · cases effect

end Belay.Sqlite.Model.NormalizedField
