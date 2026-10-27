import Belay.Sqlite.Model.OrdinaryStepEffects
import Belay.Sqlite.Model.TableByName
import Belay.Sqlite.Model.StatementRewrite

set_option doc.verso true

/-! The step laws of the statements that rewrite the catalog and keep every row (ADR 0017, S6): the
rename of a table or a column. A step of such a statement either ends the run, when the rewrite does not
keep the outline of the catalog, or succeeds with the same rows under the rewritten catalog. -/

namespace Belay.Sqlite.Model

/-- For every connection and statement that resolves to a rewrite of the catalog, and every step that
continues: the step has no error output and no further execution, the rewritten catalog has the outline
of the catalog before ({name}`Catalog.sameOutline`), and the next connection is the connection with the
rewritten catalog and the rows as they were. In plain words, a rename never fails in the model and keeps
every row; a table found in the rewritten catalog at a position holds the rows of that position before
(failure and success law). Proof sketch: the only error of the effect is
{name}`ExecutionError.unmodeled` ({name}`runScriptStep_effect_of_unmodeled`), and a success is the
guard-passing case of {name}`step` ({name}`step_rewrite_ok`). -/
theorem runScriptStep_rewrite {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {renamed : Catalog}
    (found : resolveStatement context connection.resolveState statement = .ok (.rewrite renamed, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = false ∧ others = [] ∧
      connection.state.database.catalog.sameOutline renamed = true ∧
      next = { connection with state := { connection.state with
        database := { connection.state.database with catalog := renamed } } } := by
  have unmodeled : ∀ value reason reached,
      (connection.state.statementRun value parameters (.rewrite renamed)).effect = .error (reason, reached) →
        reason = .unmodeled := by
    intro value reason reached effect
    simp only [SqlState.statementRun, runStatement, Model.step] at effect
    split at effect <;> simp_all
  obtain ⟨noError, value, database, -, effect, nextEq⟩ := runScriptStep_effect_of_unmodeled found rfl
    (by intro _ _ same; cases same) step unmodeled
  have ran : Model.step value (connection.state.counters.view (Resolved.Statement.rewrite renamed).counterReads)
      parameters (.rewrite renamed) connection.state.database = .ok database := by
    simpa [SqlState.statementRun, runStatement] using effect
  obtain ⟨-, -, outline⟩ := step_rewrite_ok _ _ _ ran
  have stored := step_rewrite_of_keeps value (connection.state.counters.view (Resolved.Statement.rewrite renamed).counterReads)
    parameters outline
  rw [ran] at stored
  cases Except.ok.inj stored
  refine ⟨noError, runScriptStep_others step found rfl, outline, ?_⟩
  rw [nextEq]
  simp [SqlState.statementRun, runStatement]

end Belay.Sqlite.Model
