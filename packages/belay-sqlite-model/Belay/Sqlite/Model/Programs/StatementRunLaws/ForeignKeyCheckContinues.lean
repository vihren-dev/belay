import Belay.Sqlite.Model.Programs.Scripts.ReadOnlyFrame
import Belay.Sqlite.Model.Programs.StatementRunLaws.ForeignKeyPragmaQuery

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every connection, values and table choice, if the pragma gives rows
({lit}`rowsOn` is {lit}`some`, so exactly one table gives rows or none does), the output of the resolved
pragma is no error and no stop of the model. In plain words, a foreign-key check whose rows the model
generates has rows or none, and never fails. Proof sketch: the output is the rows of the calm query
({name}`resolvedStepOutput_calm_unordered`), which are neither an error nor a stop. -/
theorem resolvedStepOutput_keyCheck_rows (index : Nat) (connection : Connection) (parameters : List Value)
    (table : Option Nat) (rows : List (List Value))
    (found : (Resolved.PragmaRows.foreignKeyCheck table).rowsOn connection.state.database = some rows) :
    (resolvedStepOutput none index connection parameters (keyCheckQuery table)).isError = false ∧
      ∀ reason, resolvedStepOutput none index connection parameters (keyCheckQuery table) ≠ .unmodeled reason := by
  have source := keyCheckQuery_source (Resolved.EvalContext.bound parameters) connection.state.database table rows
    found
  rw [show keyCheckQuery table = .query (pragmaQuery (.foreignKeyCheck table) foreignKeyCheckNames) [] from rfl,
    resolvedStepOutput_calm_unordered none index connection parameters (keyCheckQuery_calm table) rfl rfl rfl rfl
      rfl rfl source (by simp) rfl rfl]
  exact ⟨rfl, fun _ => nofun⟩

/-- For every context, clock, index, connection and values, if no catalog position has a foreign-key mismatch
and the pragma gives rows ({lit}`rowsOn` is {lit}`some`), the step of the database-wide
{lit}`PRAGMA foreign_key_check` continues with an output that is no error, without further executions, and the
next connection is the connection. In plain words, the check goes on, whether it finds violations or not, and
changes nothing. Proof sketch: the output of the step is that of the resolved pragma
({name}`runScriptStep_output`, {name}`resolvedStepOutput_keyCheck_clock`), which is no stop of the model
({name}`resolvedStepOutput_keyCheck_rows`), so the step continues; {name}`runScriptStep_readOnly_keeps` gives
the rest. -/
theorem runScriptStep_keyCheck_continues (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (connection : Connection) (parameters : List Value) (rows : List (List Value))
    (prepares : ∀ position < connection.state.database.catalog.length,
      connection.state.database.catalog.keyMismatch position = none)
    (found : (Resolved.PragmaRows.foreignKeyCheck none).rowsOn connection.state.database = some rows) :
    ∃ output, runScriptStep context clock index connection (.pragma (.foreignKeyCheck none)) parameters =
      .continued output connection [] ∧ output.isError = false := by
  have prepared := (resolvePragma_keyCheck_iff connection.resolveState).mpr prepares
  have resolved : resolveStatement context connection.resolveState (.pragma (.foreignKeyCheck none)) =
      .ok (keyCheckQuery none, connection.resolveState) := by
    simp only [statement_arms, resolveStatementPragma_foreignKeyCheck, prepared]
  have out := runScriptStep_output context clock index connection (.pragma (.foreignKeyCheck none)) parameters
  rw [resolved] at out
  simp only [] at out
  rw [resolvedStepOutput_keyCheck_clock] at out
  obtain ⟨noError, modeled⟩ := resolvedStepOutput_keyCheck_rows index connection parameters none rows found
  cases step : runScriptStep context clock index connection (.pragma (.foreignKeyCheck none)) parameters with
  | ended reason =>
    rw [step] at out
    exact absurd out.symm (modeled reason)
  | continued output next others =>
    rw [step] at out
    obtain ⟨rfl, rfl⟩ := runScriptStep_readOnly_keeps resolved (Or.inl ⟨_, _, rfl⟩) step
    exact ⟨output, rfl, by rw [show output = _ from out]; exact noError⟩

end Belay.Sqlite.Model
