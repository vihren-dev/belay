import Belay.Sqlite.Model.Resolution.StatementArms
import Belay.Sqlite.Model.SuccessfulScriptEffects
import Belay.Sqlite.Model.ScriptLaws

set_option doc.verso true

/-! CREATE TRIGGER as one step of a script (ADR 0017, S6). Registering a trigger changes the catalog
and the storage slots and nothing else: no trigger body runs. The module gives the connection that a
successful step reaches. -/

namespace Belay.Sqlite.Model

/-- For every catalog, trigger name and trigger: a resolution of CREATE TRIGGER without IF NOT EXISTS
gives a prepare error with the catalog unchanged, or the creation of exactly the written trigger at the
end of the catalog with the catalog that holds it. No body executes in either case. Proof sketch: split
the preparation checks of the resolver. -/
private theorem createTrigger_resolution_cases {catalog next : Catalog} {name : Identifier}
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

/-- For every connection, trigger name, trigger and error-free step of CREATE TRIGGER without IF NOT
EXISTS that continues: the next connection is the connection with the catalog that holds the trigger, an
empty storage slot appended, and some counters. In plain words, the rows of every table stay, and the
trigger may have any written body, because registration does not execute it. Clock, snapshot and both
settings stay. Proof sketch: success excludes preparation errors and the failure of the storage
alignment, leaving the single append effect. -/
theorem createTrigger_step {context : ResolveContext} {clock : Option Clock} {index : Nat}
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
    rcases createTrigger_resolution_cases bodyOk with ⟨error, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨value, database, _, effect, _⟩ := runScriptStep_effect resolution rfl step noError
      simp [SqlState.statementRun, runStatement, Belay.Sqlite.Model.step] at effect
    · obtain ⟨value, database, _, effect, advanced⟩ := runScriptStep_effect resolution rfl step noError
      simp only [SqlState.statementRun, runStatement, Belay.Sqlite.Model.step] at effect
      split at effect
      · cases effect
        exact ⟨_, advanced⟩
      · cases effect

end Belay.Sqlite.Model
