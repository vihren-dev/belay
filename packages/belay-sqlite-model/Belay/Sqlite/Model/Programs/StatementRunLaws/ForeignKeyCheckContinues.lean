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

end Belay.Sqlite.Model
