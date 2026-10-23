import Belay.Sqlite.Model.StatementCountersLaws

set_option doc.verso true

/-! A run does not depend on the counters of its connection that its statements do not read
(ADR 0024, D1 and D2). A connection that knows fewer counters takes the same steps as one that
knows more, while the first connection runs: the same outputs, and next connections that again
know fewer counters. A statement that reads a counter that its connection does not know ends the
run, so the law holds for the runs that do not end. The laws for one statement are in
{lit}`StatementCountersLaws.lean`. -/

namespace Belay.Sqlite.Model

/-- What a step of a run gives when the first connection knows fewer counters: either the first
run ends, or both runs continue with the same output and with connections where the first knows
fewer counters. -/
def RunStep.LessKnown : RunStep → RunStep → Prop
  | .ended _, _ => True
  | .continued firstOutput first, .continued secondOutput second =>
    firstOutput = secondOutput ∧ first.LessKnown second
  | .continued .., .ended _ => False

/-- For every connection pair in the relation {name}`Connection.LessKnown`, every after-state,
counts and transition pair in the relation {name}`SqlTransition.LessKnown`: the connections after
the step are in the relation. Proof sketch: a transition that continues gives its state; a halt
gives the database of its outcome, which is the same on both sides, and the counters after the
counts ({name}`Counters.LessKnown.apply`). -/
theorem Connection.afterStep_counters {first second : Connection} (after : ResolveState) (counts : Counts)
    {firstStep secondStep : SqlTransition} (same : first.LessKnown second)
    (steps : firstStep.LessKnown secondStep) :
    (first.afterStep after counts firstStep).LessKnown (second.afterStep after counts secondStep) := by
  obtain ⟨⟨database, snapshot, clockOf, counters⟩, _, _⟩ := same
  cases firstStep <;> cases secondStep
  · exact ⟨steps, rfl, rfl⟩
  · exact absurd steps id
  · exact absurd steps id
  · simp only [SqlTransition.LessKnown] at steps
    subst steps
    rename_i outcome
    cases outcome <;>
      exact ⟨⟨rfl, rfl, clockOf, counters.apply counts⟩, rfl, rfl⟩

/-- For every context, clock, index, statement and values, and two connections where the first knows
fewer counters: the step of {name}`runScriptStep` on the first connection is in the relation
{name}`RunStep.LessKnown` with the step on the second. So a step that the first connection takes
without ending gives the same output on the second, and again connections in the relation. Proof
sketch: resolution, the clock value and the support check read the database, the snapshot and the
settings, which are the same; a first connection that does not end the run knows every counter that
the statement reads, so the run of the statement is the same on both
({name}`SqlState.statementRun_counters`); the output and the next connection follow from
{name}`Output.ofStep_counters`, {name}`advanceRun_counters` and {name}`Connection.afterStep_counters`. -/
theorem runScriptStep_counters (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {first second : Connection} (same : first.LessKnown second) (statement : Syntax.Statement)
    (parameters : List Value) :
    (runScriptStep context clock index first statement parameters).LessKnown
      (runScriptStep context clock index second statement parameters) := by
  have resolving : first.resolveState = second.resolveState := by
    obtain ⟨⟨database, snapshot, _⟩, settings, recursive⟩ := same
    simp only [Connection.resolveState, database, snapshot, settings, recursive]
  unfold runScriptStep runScriptStepWith
  rw [resolving]
  cases resolveStatement context second.resolveState statement with
  | error restriction => simp [RunStep.LessKnown]
  | ok resolvedAfter =>
    obtain ⟨resolved, after⟩ := resolvedAfter
    simp only
    cases statementClock clock index resolved with
    | none => simp [RunStep.LessKnown]
    | some value =>
      cases known : first.state.counters.firstUnknown resolved.counterReads with
      | some kind => simp [RunStep.LessKnown]
      | none =>
        have run := SqlState.statementRun_counters same.1 value parameters resolved known
        have secondKnown := (same.1.2.2.2.view_eq known).2
        simp only [secondKnown, run]
        by_cases ready : (first.state.statementRun value parameters resolved).ready = true
        · have steps := advanceRun_counters index resolved (first.state.statementRun value parameters resolved) same.1
          have output := Output.ofStep_counters value parameters resolved
            (first.state.statementRun value parameters resolved) same.1 known steps
          simp only [ready, Bool.not_true, Bool.false_eq_true, ite_false, ranScriptStep, output]
          split
          · simp [RunStep.LessKnown]
          all_goals
            simp only [RunStep.LessKnown]
            exact ⟨trivial, Connection.afterStep_counters after _ same steps⟩
        · simp [ready, RunStep.LessKnown]

/-- For every context, clock, statements with values, and two connections where the first knows
fewer counters: if no output of the run on the first connection ends the run
({name}`Output.endsRun`), the runs ({name}`runScriptFrom`) have the same outputs, and end on
connections where the first knows fewer counters. So a script that does not read an unknown counter
has the same outputs on a connection that knows no counter as on one that knows them. Proof sketch:
induction on the statements, with {name}`runScriptStep_counters` for each step; a step that ends
the run has the output {name}`Output.unmodeled`, which ends the run. -/
theorem runScriptFrom_counters (context : ResolveContext) (clock : Option Clock) :
    ∀ (script : List (Syntax.Statement × List Value)) (index : Nat) {first second : Connection},
      first.LessKnown second →
        (∀ output ∈ (runScriptFrom context clock index first script).outputs, output.endsRun = false) →
        (runScriptFrom context clock index first script).outputs =
            (runScriptFrom context clock index second script).outputs ∧
          (runScriptFrom context clock index first script).connection.LessKnown
            (runScriptFrom context clock index second script).connection
  | [], _, _, _, same, _ => ⟨rfl, same⟩
  | (statement, parameters) :: rest, index, first, second, same, modeled => by
    have step := runScriptStep_counters context clock index same statement parameters
    unfold runScriptFrom at modeled ⊢
    cases firstStep : runScriptStep context clock index first statement parameters with
    | ended reason =>
      simp [firstStep, Output.endsRun] at modeled
    | continued output next =>
      cases secondStep : runScriptStep context clock index second statement parameters with
      | ended other => rw [firstStep, secondStep] at step; exact absurd step id
      | continued otherOutput otherNext =>
        rw [firstStep, secondStep] at step
        obtain ⟨sameOutput, sameNext⟩ := step
        subst sameOutput
        simp only [firstStep] at modeled ⊢
        have later := runScriptFrom_counters context clock rest (index + 1) sameNext
          (fun output member => modeled output (List.mem_cons_of_mem _ member))
        exact ⟨by simp only [later.1], later.2⟩

end Belay.Sqlite.Model
