import Belay.Sqlite.Model.Programs.Scripts.CatalogChangeRules
import Belay.Sqlite.Model.Schema.Ddl.DropTableResolution
import Belay.Sqlite.Model.Programs.Scripts.OrdinaryStepEffects
import Belay.Sqlite.Model.Schema.Ddl.TableByName

set_option doc.verso true

/-! The step laws of DROP TABLE (ADR 0017, S6): what one step of a resolved drop does to the connection.
With foreign keys off the drop is plain: it deletes no rows, so it cannot fail and it keeps every table
that it does not drop. With foreign keys on, DROP TABLE runs an implicit DELETE of the table, and a
foreign-key action can then change a table that the statement does not name; the laws for that case
state what stays true without a premise about the actions. -/

namespace Belay.Sqlite.Model

/-- For every connection and statement that resolves to a drop with rules (foreign keys on, or trigger
programs), and every step that continues without an error output: the database of the next connection is
the success of the key run ({name}`dropKeys`) at some clock value, and it has the catalog without the
dropped objects. In plain words, the catalog after DROP TABLE with foreign keys on is the same as with
them off; the rows depend on the actions of the keys, so the law names them only through the key run, and
nothing else of the connection changes except the counters. Proof sketch: {name}`runScriptStep_effect`
gives the successful effect, which is the effect of {name}`dropKeys`, and {name}`dropKeys_ok_catalog` reads
its catalog. -/
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
  obtain ⟨value, database, -, effect, nextEq⟩ := runScriptStep_effect found rfl step noError
  simp only [SqlState.statementRun, runStatement, StatementRun.withKeys] at effect
  refine ⟨value, connection.state.counters.apply
    (connection.state.statementRun value parameters (.drop positions (some rules))).counts, ?_, ?_, ?_⟩
  · rw [nextEq]
    simpa using effect
  · rw [nextEq]
    exact dropKeys_ok_catalog (by simpa using effect)
  · rw [nextEq]

/-- For every connection and statement that resolves to a drop with rules, and every step that continues
with an error output: if no error of the key run ({name}`dropKeys`) is a stop of the FAIL or ROLLBACK
algorithm, the next connection is the connection with the counters of the run and nothing else changed.
In plain words, a failed DROP TABLE with foreign keys on keeps the database; the premise excludes the
stop of a row by RAISE(FAIL) or RAISE(ROLLBACK) of a trigger, the only way that the key run keeps part
of its work or rolls back. The law does not say that the premise holds: it holds for a drop without
rules, where no step fails ({name}`runScriptStep_dropPlain_eq`). Proof sketch:
{name}`runScriptStep_failed_frame` with the premise as its error frame. -/
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
  refine runScriptStep_failed_frame found rfl (by intro _ _ same; cases same) step failed fun value reason reached effect => ?_
  simp only [SqlState.statementRun, runStatement, StatementRun.withKeys] at effect
  exact noStop value reason reached (by simpa using effect)

end Belay.Sqlite.Model
