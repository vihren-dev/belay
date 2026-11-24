import Belay.Sqlite.Model.Programs.Scripts.ExecutionEffects
import Belay.Sqlite.Model.Programs.Scripts.StepCatalogLiteral
import Belay.Sqlite.Model.Programs.Scripts.FailedStepFrame

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every continuing statement and each of its executions with a non-error output,
the next connection has the resolution state returned by {name}`resolveStatement`.
This includes every production of an INSERT from a query. An error imposes no condition.
Proof sketch: a successful ordinary step has the catalog of its resolved effect. The
alternative productions of an INSERT change only its target rows. Transaction control
and setting statements have one execution, whose snapshot and settings follow the
transition of the resolver. -/
theorem runScriptStep_resolveState {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {c next : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {others : List StatementExecution} {resolved : Resolved.Statement} {after : ResolveState}
    (found : resolveStatement context c.resolveState statement = .ok (resolved, after))
    (step : runScriptStep context clock index c statement parameters = .continued output next others)
    {execution : StatementExecution} (member : execution ∈ (RunStep.continued output next others).executions)
    (ok : execution.output.isError = false) : execution.next.resolveState = after := by
  have stateEq := (resolveStatement_certificate context _ _ _ _ found).after
  by_cases single : resolved.fromQuery = false
  · obtain rfl := runScriptStep_others step found single
    simp only [RunStep.executions, List.mem_singleton] at member
    subst execution
    change next.resolveState = after
    change output.isError = false at ok
    by_cases ordinary : resolved.isControl = false
    · obtain ⟨value, database, _, success, rfl⟩ := runScriptStep_effect found ordinary step ok
      have notSetting : ∀ setting on, resolved ≠ .setting setting on := by
        intro setting on equal
        subst resolved
        cases ordinary
      have catalog := (literalStep_success_catalog notSetting success).1
      rw [stateEq, ResolveState.after_of_isControl _ ordinary]
      simp [Connection.resolveState, catalog]
    · obtain ⟨actual, after', value, same, _, _, _, observed, transition⟩ := runScriptStep_ran step
      rw [found] at same
      cases same
      rw [transition, stateEq]
      rw [observed] at ok
      cases resolved <;> try contradiction
      all_goals try cases ‹Syntax.PragmaSetting›
      all_goals cases snapshot : c.state.snapshot <;>
        simp [Resolved.Statement.isControl, ResolveState.after, ResolveState.set, Connection.resolveState,
          Connection.afterStep, advanceRun, advanceWith, SqlTransition.counted, snapshot, SqlState.statementRun,
          runStatement, Model.step, SqlState.publish, Output.ofStep, haltError, SqlState.finish, Output.isError] at *
  · obtain ⟨target, cells, source, clauses, returning, algorithm, subqueries, rfl⟩ :=
      Resolved.Statement.fromQuery_form (by simpa using single)
    obtain ⟨rows, counters, written⟩ := runScriptStep_insertSelect_frame step found execution member ok
    rw [written, stateEq]
    rfl

end Belay.Sqlite.Model
