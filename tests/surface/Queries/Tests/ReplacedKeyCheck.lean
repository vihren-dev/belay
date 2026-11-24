import Belay

set_option doc.verso true

/-! Retention witnesses for the two foreign-key pragma step statements replaced in slice 5. -/

namespace Belay.Sqlite.Model.ReplacedKeyCheck

/-- The former law {lit}`runScriptStep_keyCheck_resolved`. For every statement that resolves to a foreign-key check and every database on
which the model describes its rows, the step succeeds once and retains the whole
connection. The output can list violations. Proof sketch: the resolved check has a
modeled output without an error. The query rule shows that every continuing case has one execution and keeps the connection. -/
theorem runScriptStep_keyCheck_resolved {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {table : Option Nat} {after : ResolveState} {rows : List (List Value)}
    (resolved : resolveStatement context connection.resolveState statement = .ok (keyCheckQuery table, after))
    (found : (Resolved.PragmaRows.foreignKeyCheck table).rowsOn connection.state.database = some rows) :
    ∃ output, runScriptStep context clock index connection statement parameters =
      .continued output connection [] ∧ output.isError = false := by
  have out := runScriptStep_output context clock index connection statement parameters
  rw [resolved] at out
  simp only [] at out
  rw [resolvedStepOutput_keyCheck_clock] at out
  obtain ⟨noError, modeled⟩ := resolvedStepOutput_keyCheck_rows index connection parameters table rows found
  cases step : runScriptStep context clock index connection statement parameters with
  | ended reason =>
    rw [step] at out
    exact absurd out.symm (modeled reason)
  | continued output next others =>
    rw [step] at out
    have frame := RunStep.of_rule (runScriptStep_query_eq resolved)
      (property := fun _ reached more => more = [] ∧ reached = connection)
      (by
        generalize pragmaQuery (.foreignKeyCheck table) foreignKeyCheckNames = q
        dsimp only
        repeat' first | exact ⟨rfl, rfl⟩ | exact True.intro | split) step
    obtain ⟨rfl, rfl⟩ := frame
    exact ⟨output, rfl, by rw [show output = _ from out]; exact noError⟩

/-- The former law {lit}`runScriptStep_keyCheck_continues`. For every context, clock, index, connection and values, if no catalog position has a foreign-key mismatch
and the pragma gives rows ({lit}`rowsOn` is {lit}`some`), the step of the database-wide
{lit}`PRAGMA foreign_key_check` continues with an output that is no error, without further executions, and the
next connection is the connection. In plain words, the check goes on, whether it finds violations or not, and
changes nothing. Proof sketch: the output of the step is that of the resolved pragma
({name}`runScriptStep_output`, {name}`resolvedStepOutput_keyCheck_clock`), which is no stop of the model
({name}`resolvedStepOutput_keyCheck_rows`), so the step continues; the query rule gives
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
  exact runScriptStep_keyCheck_resolved resolved found

#print axioms runScriptStep_keyCheck_resolved
#print axioms runScriptStep_keyCheck_continues

end Belay.Sqlite.Model.ReplacedKeyCheck
