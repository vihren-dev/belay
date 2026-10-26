import ContextCore
import Belay.Sqlite.Model.ScriptRunDerived

set_option doc.verso true

/-! An isolated experiment for one surface preservation induction. A guarded
obligation admits conditions supplied by callers and conditions derived from
the current invariant, while using the actual selected clock and ready gate. -/

namespace Belay.Sqlite.Model.ContextExperiment

/-- For the given surface step, every successful resolution with a selected
clock and a ready state run meets the execution condition. Failure to resolve,
a missing clock, or a failed support check requires nothing. -/
def StepCondition (condition : Condition) (context : ResolveContext) (clock : Option Clock)
    (index : Nat) (connection : Connection) (statement : Syntax.Statement)
    (parameters : List Value) : Prop :=
  ∀ resolved after value,
    resolveStatement context connection.resolveState statement = .ok (resolved, after) →
    statementClock clock index resolved = some value →
    (SqlState.statementRun connection.state value parameters resolved).ready = true →
    condition value (connection.state.counters.view resolved.counterReads)
      parameters resolved connection.state.database

/-- For the given surface run, every reached step meets its contextual condition
if the current state and its snapshot have the property. The empty script and a
suffix after an ended step require nothing. A state lacking the property imposes
no condition at that step; a continuing step still imposes the obligations of
its suffix. The property guard allows explicit and invariant-derived conditions. -/
def ScriptObligations (property : Database → Prop) (condition : Condition)
    (context : ResolveContext) (clock : Option Clock) (index : Nat) (connection : Connection) :
    List (Syntax.Statement × List Value) → Prop
  | [] => True
  | (statement, parameters) :: rest =>
    (connection.state.Holds property →
      StepCondition condition context clock index connection statement parameters) ∧
      match runScriptStep context clock index connection statement parameters with
      | .ended _ => True
      | .continued _ next => ScriptObligations property condition context clock (index + 1) next rest

/-- For every property, contextual condition and surface step, a preservation
rule, the property on the state and snapshot, and the step condition imply that
every connection returned by a continuing step has the property and snapshot
property. An ended step has no returned connection to constrain.
Proof sketch: successful gates give the actual clock and readiness. Apply the
effect rule and the existing transition-to-connection transport lemma. -/
theorem surface_step_keeps {property : Database → Prop} {condition : Condition}
    (keeps : Keeps property condition) (context : ResolveContext)
    (clock : Option Clock) (index : Nat) {connection : Connection}
    (holds : connection.state.Holds property) (statement : Syntax.Statement)
    (parameters : List Value)
    (met : StepCondition condition context clock index connection statement parameters)
    {output : Output} {next : Connection}
    (continued : runScriptStep context clock index connection statement parameters = .continued output next) :
    next.state.Holds property := by
  unfold runScriptStep runScriptStepWith ranScriptStep at continued
  split at continued
  · nomatch continued
  · rename_i resolved after resolvedEq
    split at continued
    · nomatch continued
    · rename_i value clockEq
      split at continued
      · nomatch continued
      · dsimp only at continued
        split at continued
        · nomatch continued
        · rename_i passes
          have ready : (connection.state.statementRun value parameters resolved).ready = true := by
            simpa using passes
          split at continued
          · nomatch continued
          all_goals
            injection continued with _ same
            subst same
            exact Connection.afterStep_holds connection _ _
              (SqlTransition.counted_holds _ (advanceWith_holds index resolved holds
                (keeps value _ parameters resolved _ holds.1
                  (met resolved after value resolvedEq clockEq ready))))

/-- For every contextual preservation rule and surface run, if its entry state
and snapshot have the property and its guarded obligations hold, the final
connection state and snapshot have it. An ended step retains the current state.
Proof sketch: one script induction uses {name}`surface_step_keeps`. The guarded
condition becomes usable from the induction invariant at each reached state. -/
theorem surface_run_keeps {property : Database → Prop} {condition : Condition}
    (keeps : Keeps property condition) (context : ResolveContext) (clock : Option Clock) :
    ∀ (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value)),
      connection.state.Holds property →
      ScriptObligations property condition context clock index connection script →
      (runScriptFrom context clock index connection script).connection.state.Holds property
  | _, _, [], holds, _ => holds
  | index, connection, (statement, parameters) :: rest, holds, conditions => by
    have step : ∀ output next,
        runScriptStep context clock index connection statement parameters = .continued output next →
          next.state.Holds property := fun _ _ =>
      surface_step_keeps keeps context clock index holds statement parameters (conditions.1 holds)
    have later := conditions.2
    unfold runScriptFrom
    revert step later
    cases runScriptStep context clock index connection statement parameters with
    | ended _ => exact fun _ _ => holds
    | continued output next =>
      exact fun step later =>
        surface_run_keeps keeps context clock (index + 1) rest (step output next rfl) later

#print axioms surface_step_keeps
#print axioms surface_run_keeps

end Belay.Sqlite.Model.ContextExperiment
