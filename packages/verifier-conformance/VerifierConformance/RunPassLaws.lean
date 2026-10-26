import VerifierConformance.Classify
import Belay.Sqlite.Model.ScriptRunSingleton

set_option doc.verso true

/-! The laws that make the evidence of the passes that continue evidence for the model's complete
executions ({name}`Belay.Sqlite.Model.runScriptAllFrom`). They are a module apart from
{name}`Belay.Sqlite.Model.Conformance.runPassAllFrom`, so that the classifier of the cases does not
import them: a mutant copy of the model ({lit}`conformance.resolve_mutants`) then builds also when
the mutant breaks these proofs. -/

namespace Belay.Sqlite.Model.Conformance

/-- For every verdict, the verdict of one execution with it ({name}`Verdict.ofExecutions`) is the
verdict. So a case with one complete execution is classified as it was before the model listed
executions. Proof sketch: case analysis on the verdict. -/
theorem Verdict.ofExecutions_singleton (verdict : Verdict) : Verdict.ofExecutions [verdict] = verdict := by
  cases verdict <;> simp [Verdict.ofExecutions]

/-- Whether a step of the pass and a step of the model's run are the same step: both end the run with
the same reason, or both continue and their executions have the same outputs and the same next
connections, in the same order. -/
def RunPassStep.Matches : RunPassStep → RunStep → Prop
  | .ended passReason, .ended modelReason => passReason = modelReason
  | .continued executions, stepped@(.continued ..) =>
    executions.map (fun execution => (execution.result, execution.next)) =
      stepped.executions.map (fun execution => (execution.output, execution.next))
  | .ended _, .continued .. => False
  | .continued _, .ended _ => False

/-- For every function from a connection to passes and to runs of the model that have the same results
and outputs, and every list of entries of the pass and of the executions of the model with the same
results, outputs and next connections: the results of the passes of the rest from each entry, each
with the result of its entry first, are the outputs of the runs of the rest from each execution, each
with the output of its execution first. Proof sketch: induction on the two lists; the heads agree, and
the results of the rest map through the same prefix. -/
theorem flatMap_results_eq (passes : Connection → List RunPass) (scripts : Connection → List ScriptRun)
    (later : ∀ connection, (passes connection).map (·.results) = (scripts connection).map (·.outputs)) :
    ∀ (entries : List ExecutionPass) (executions : List StatementExecution),
      entries.map (fun entry => (entry.result, entry.next)) =
        executions.map (fun execution => (execution.output, execution.next)) →
      (entries.flatMap fun entry => (passes entry.next).map fun pass => entry.result :: pass.results) =
        executions.flatMap fun execution => (scripts execution.next).map fun run => execution.output :: run.outputs
  | [], [], _ => rfl
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same
  | entry :: entries, execution :: executions, same => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at same
    obtain ⟨⟨sameResult, sameNext⟩, rest⟩ := same
    have tail := flatMap_results_eq passes scripts later entries executions (by simpa using rest)
    have head : (passes entry.next).map (fun pass => entry.result :: pass.results) =
        (scripts execution.next).map (fun run => execution.output :: run.outputs) := by
      have mapped := congrArg (List.map (entry.result :: ·)) (later entry.next)
      simp only [List.map_map, Function.comp_def] at mapped
      rw [mapped, sameNext, sameResult]
    simp only [List.flatMap_cons, head, tail]

/-- For every step function of the pass and of the model's run that give matching steps
({name}`RunPassStep.Matches`) at every index, connection and statement, and every index, connection and
statements: the results of the passes ({name}`runPassAllWith`) are the outputs of the complete executions
({name}`runScriptAllWith`), in the same order. Proof sketch: induction on the statements; both lists are
the executions of the step with the executions of the rest from each connection, and the matching
steps list the same outputs and connections. -/
theorem runPassAllWith_results {passStep : Nat → Connection → Syntax.Statement × List Value → RunPassStep}
    {modelStep : Nat → Connection → Syntax.Statement × List Value → RunStep}
    (matching : ∀ index connection entry, (passStep index connection entry).Matches (modelStep index connection entry)) :
    ∀ (script : List (Syntax.Statement × List Value)) (index : Nat) (connection : Connection),
      (runPassAllWith passStep index connection script).map (·.results) =
        (runScriptAllWith modelStep index connection script).map (·.outputs)
  | [], _, _ => rfl
  | entry :: rest, index, connection => by
    have same := matching index connection entry
    unfold runPassAllWith runScriptAllWith
    cases passed : passStep index connection entry with
    | ended reason =>
      cases stepped : modelStep index connection entry with
      | ended other => simp only [passed, stepped, RunPassStep.Matches] at same; subst same; rfl
      | continued output next others => simp [passed, stepped, RunPassStep.Matches] at same
    | continued executions =>
      cases stepped : modelStep index connection entry with
      | ended other => simp [passed, stepped, RunPassStep.Matches] at same
      | continued output next others =>
        simp only [passed, stepped, RunPassStep.Matches] at same ⊢
        generalize (RunStep.continued output next others).executions = found at same ⊢
        simp only [List.map_flatMap, List.map_map, Function.comp_def]
        exact flatMap_results_eq (fun connection => runPassAllWith passStep (index + 1) connection rest)
          (fun connection => runScriptAllWith modelStep (index + 1) connection rest)
          (fun connection => runPassAllWith_results matching rest (index + 1) connection) executions found same

/-- For every context, clock, index, connection and statements with their values, the step of the pass
({name}`runPassStep`) matches the step of the model's run ({name}`runScriptStep`). Proof sketch: both
take the same steps of {name}`runScriptStepWith` and the same {name}`ranScriptStep`; the further
executions of that step are those of the alternatives of the run ({name}`ranScriptStep_continued`),
which the pass lists with their runs. -/
theorem runPassStep_matches (context : ResolveContext) (clock : Option Clock) (index : Nat) (connection : Connection)
    (statement : Syntax.Statement) (parameters : List Value) :
    (runPassStep context clock index connection statement parameters).Matches
      (runScriptStep context clock index connection statement parameters) := by
  simp only [runPassStep, runScriptStep, runScriptStepWith]
  repeat' split
  all_goals first | exact rfl | skip
  all_goals
    unfold ranPassStep
    cases stepped : ranScriptStep index parameters connection _ _ _ _ _ with
    | ended reason => exact rfl
    | continued output next others =>
      obtain ⟨further, listed, same⟩ := ranScriptStep_continued stepped
      simp only [listed, RunPassStep.Matches, RunStep.executions, ExecutionPass.ofExecution, same, List.map_cons,
        List.map_map, Function.comp_def]

/-- For every context, optional clock, index, connection and statements with their values, the results
of the passes ({name}`runPassAllFrom`) are the outputs of the complete executions of the model's run
({name}`runScriptAllFrom`), in the same order. So a verdict that compares the passes with SQLite
compares the executions of the model. Proof sketch: {name}`runPassAllWith_results` with
{name}`runPassStep_matches`. -/
theorem runPassAllFrom_results (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (connection : Connection) (script : List (Syntax.Statement × List Value)) :
    (runPassAllFrom context clock index connection script).map (·.results) =
      (runScriptAllFrom context clock index connection script).map (·.outputs) :=
  runPassAllWith_results (fun index connection (statement, parameters) =>
    runPassStep_matches context clock index connection statement parameters) script index connection

/-- For every context, optional clock, index, connection and statements with their values, the results
of the pass of the model's own execution ({name}`runPassFrom`), from which a prediction comes, are the
outputs of the model's run ({name}`runScriptFrom`). Proof sketch: the complete executions are the one run
of the model ({name}`runScriptAllFrom_eq`), so the passes are one pass, and {name}`runPassAllFrom_results`
gives its results. -/
theorem runPassFrom_results (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (connection : Connection) (script : List (Syntax.Statement × List Value)) :
    (runPassFrom context clock index connection script).results =
      (runScriptFrom context clock index connection script).outputs := by
  have results := runPassAllFrom_results context clock index connection script
  rw [runScriptAllFrom_eq] at results
  unfold runPassFrom
  cases passes : runPassAllFrom context clock index connection script with
  | nil => simp [passes] at results
  | cons pass others => simp [passes] at results; simp [results.1]

end Belay.Sqlite.Model.Conformance
