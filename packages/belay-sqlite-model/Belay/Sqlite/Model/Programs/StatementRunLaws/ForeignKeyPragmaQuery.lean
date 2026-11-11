import Belay.Sqlite.Model.Programs.StatementRunLaws.SelectCalmRule
import Belay.Sqlite.Model.Schema.Rows.ForeignKeyPragmaQuery

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every connection, table choice, statement index and bound values, the resolved
foreign-key pragma has no rows exactly when its generated rows are the empty list. A missing
generation result is unmodeled and does not count as empty. This concerns the prepared query;
the catalog mismatch check is separate. Proof sketch: the pragma is a calm query without order or window
({name}`resolvedStepOutput_calm_unordered`); its source is exactly the generated rows, and it has no WHERE condition. -/
theorem resolvedStepOutput_keyCheck_hasNoRows (index : Nat) (connection : Connection)
    (parameters : List Value) (table : Option Nat) :
    (resolvedStepOutput none index connection parameters (keyCheckQuery table)).hasNoRows = true ↔
      (Resolved.PragmaRows.foreignKeyCheck table).rowsOn connection.state.database = some [] := by
  let query := pragmaQuery (.foreignKeyCheck table) foreignKeyCheckNames
  change (resolvedStepOutput none index connection parameters (.query query [])).hasNoRows = true ↔ _
  have calm := keyCheckQuery_calm table
  cases found : (Resolved.PragmaRows.foreignKeyCheck table).rowsOn connection.state.database with
  | none =>
    rw [resolvedStepOutput_query index connection parameters query [] calm.readsClock (calm.firstUnknown _)]
    have source : query.source (connection.queryContext parameters query []) connection.state.database = none := by
      simp [query, pragmaQuery, Resolved.Query.source, Resolved.QuerySource.join, found, List.foldlM]
    have ran : query.runOn 0 (connection.state.counters.view (Resolved.Statement.query query []).counterReads)
        parameters connection.state.database [] = none := by
      change (query.source (connection.queryContext parameters query []) connection.state.database).map _ = none
      rw [source]
      rfl
    simp only [Resolved.Query.described, Resolved.Query.outputOn, ran]
    split <;> simp [Output.hasNoRows]
  | some rows =>
    have source := keyCheckQuery_source (Resolved.EvalContext.bound parameters) connection.state.database table rows found
    rw [resolvedStepOutput_calm_unordered none index connection parameters calm rfl rfl rfl rfl rfl rfl source
      (by simp) rfl rfl, Resolved.Query.results_plain_unordered _ rfl rfl rfl rfl rfl rfl]
    simp [Output.hasNoRows, pragmaQuery, Resolved.filtered, (Resolved.normalForm_perm _).isEmpty_eq,
      List.eq_nil_iff_forall_not_mem]

/-- For every clock, index, connection, values and table choice, the foreign-key pragma
has the same resolved output as a run without a clock. It reads no clock expression.
Proof sketch: the clock guard therefore supplies 0 in both executions. -/
theorem resolvedStepOutput_keyCheck_clock (clock : Option Clock) (index : Nat)
    (connection : Connection) (parameters : List Value) (table : Option Nat) :
    resolvedStepOutput clock index connection parameters (keyCheckQuery table) =
      resolvedStepOutput none index connection parameters (keyCheckQuery table) := by
  simp only [resolvedStepOutput, statementClock, (keyCheckQuery_calm table).readsClock,
    Bool.false_eq_true, ite_false]

end Belay.Sqlite.Model
