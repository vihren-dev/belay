import Belay

set_option doc.verso true

/-! ADR 0033 retention of the former write laws with their original premises. -/

namespace Belay.Sqlite.Model.ReplacedWriteModes
open Resolved

/-- The former {lit}`runScriptStep_drop_keys`. A successful DROP with rules installs the database of its key run and removes the positions from the catalog. Proof sketch: take the successful case of the registered rule and apply the key-run catalog fact. -/
theorem runScriptStep_drop_keys {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {positions : List Nat} {rules : Resolved.WriteRules}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop positions (some rules), after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (noError : output.isError = false) :
    ∃ value counters, (dropKeys rules value positions connection.state.database).effect = .ok next.state.database ∧
      next.state.database.catalog = connection.state.database.catalog.drop positions ∧
      next = { connection with state := { connection.state with database := next.state.database, counters } } := by
  rw [runScriptStep_dropWithRules_eq found] at step
  dsimp only at step
  repeat' first | split at step | contradiction
  all_goals cases step
  all_goals first
    | contradiction
    | exact ⟨_, _, by assumption, dropKeys_ok_catalog (by assumption), rfl⟩

#print axioms runScriptStep_drop_keys

/-- The former {lit}`runScriptStep_drop_failed`. A failed DROP with rules changes only counters when its program never stops with FAIL or ROLLBACK. Proof sketch: compute the error branch and eliminate those two reasons. -/
theorem runScriptStep_drop_failed {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {positions : List Nat} {rules : Resolved.WriteRules}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop positions (some rules), after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (failed : output.isError = true)
    (noStop : ∀ value reason reached, (dropKeys rules value positions connection.state.database).effect =
      .error (reason, reached) → reason ≠ .constraintFail ∧ reason ≠ .constraintRollback) :
    ∃ value, next = { connection with state := { connection.state with
        counters := connection.state.counters.apply
          (connection.state.statementRun value parameters (.drop positions (some rules))).counts } } := by
  rw [runScriptStep_dropWithRules_eq found] at step
  dsimp only at step
  repeat' first | split at step | contradiction
  all_goals cases step
  all_goals first
    | contradiction
    | rename_i value _ _ _ _ _ reason reached result eff
      obtain ⟨nofail, norollback⟩ := noStop value reason reached result
      refine ⟨value, ?_⟩
      simp [Connection.afterWriteError, Connection.afterError_failed, nofail, norollback,
        Connection.resolveState, Connection.afterWrite, SqlState.statementRun, runStatement, StatementRun.withKeys]

#print axioms runScriptStep_drop_failed

end Belay.Sqlite.Model.ReplacedWriteModes
