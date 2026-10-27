import Belay.Sqlite.Model.StatementCountersLaws
import Belay.Sqlite.Model.StatementExecution

set_option doc.verso true

/-! Executions on a connection that knows fewer counters (ADR 0017, S6; ADR 0019, D4). A statement
that does not read an unknown counter gives the same executions on a connection that knows fewer
counters: the same outputs, and next connections where the first knows fewer counters. This holds
for the execution of the model's own run and for the further executions of the alternatives of the
run. -/

namespace Belay.Sqlite.Model

/-- The relation between an execution on a connection that knows fewer counters and an execution on
one that knows more: the same output, and next connections where the first knows fewer counters
({name}`Connection.LessKnown`). -/
def StatementExecution.LessKnown (first second : StatementExecution) : Prop :=
  first.output = second.output ∧ first.next.LessKnown second.next

/-- The relation {name}`StatementExecution.LessKnown` between two lists of executions, position by
position. Two lists of different length are not in the relation. -/
def StatementExecution.LessKnownAll : List StatementExecution → List StatementExecution → Prop
  | [], [] => True
  | [], _ :: _ | _ :: _, [] => False
  | first :: firsts, second :: seconds => first.LessKnown second ∧ StatementExecution.LessKnownAll firsts seconds

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

/-- The relation between the results of {name}`StatementExecution.ofRun` on two connections: both
give an execution and the executions are in the relation {name}`StatementExecution.LessKnown`, or
both fail with the same reason. -/
def StatementExecution.OfRunLessKnown : Except String StatementExecution → Except String StatementExecution → Prop
  | .ok first, .ok second => first.LessKnown second
  | .error first, .error second => first = second
  | .ok _, .error _ | .error _, .ok _ => False

/-- For every values, statement, resolution state, clock value and run, two connections where the
first knows fewer counters and knows every counter that the statement reads, and two transitions in
the relation {name}`SqlTransition.LessKnown`: the results of {name}`StatementExecution.ofRun` are in
the relation {name}`StatementExecution.OfRunLessKnown`. Proof sketch: the outputs are equal
({name}`Output.ofStep_counters`), so both fail with one reason or both give one output, and then
{name}`Connection.afterStep_counters` relates the next connections. -/
theorem StatementExecution.ofRun_counters (parameters : List Value) {first second : Connection}
    (same : first.LessKnown second) (resolved : Resolved.Statement) (after : ResolveState) (value : Int)
    (run : StatementRun) {firstStep secondStep : SqlTransition}
    (known : first.state.counters.firstUnknown resolved.counterReads = none)
    (steps : firstStep.LessKnown secondStep) :
    StatementExecution.OfRunLessKnown (StatementExecution.ofRun parameters first resolved after value run firstStep)
      (StatementExecution.ofRun parameters second resolved after value run secondStep) := by
  unfold StatementExecution.ofRun
  rw [Output.ofStep_counters value parameters resolved run same.1 known steps]
  generalize Output.ofStep value parameters resolved second.state run secondStep = output
  cases output
  all_goals first
    | exact rfl
    | exact ⟨rfl, Connection.afterStep_counters after run.counts same steps⟩

/-- The relation between the further executions of a run on two connections: both give a list of
executions that are in the relation {name}`StatementExecution.LessKnownAll`, or both fail with the
same reason. -/
def StatementExecution.AlternativesLessKnown :
    Except String (List StatementExecution.Traced) → Except String (List StatementExecution.Traced) → Prop
  | .ok first, .ok second =>
    StatementExecution.LessKnownAll (first.map StatementExecution.Traced.execution)
      (second.map StatementExecution.Traced.execution)
  | .error first, .error second => first = second
  | .ok _, .error _ | .error _, .ok _ => False

/-- For every two results of {name}`StatementExecution.ofRun` in the relation
{name}`StatementExecution.OfRunLessKnown` and two lists of further executions in the relation
{name}`StatementExecution.AlternativesLessKnown`: the lists with the first result put in front, each
under its own trace, are in the relation. Proof sketch: cases on the results; a failure of either
side is the failure of the whole list. -/
theorem StatementExecution.AlternativesLessKnown.cons {firstHead secondHead : Except String StatementExecution}
    (head : StatementExecution.OfRunLessKnown firstHead secondHead)
    (firstTrace secondTrace : StatementExecution → StatementExecution.Traced)
    (firstOf : ∀ execution, (firstTrace execution).execution = execution)
    (secondOf : ∀ execution, (secondTrace execution).execution = execution)
    {firstTail secondTail : Except String (List StatementExecution.Traced)}
    (tails : StatementExecution.AlternativesLessKnown firstTail secondTail) :
    StatementExecution.AlternativesLessKnown
      (do let head ← Except.map firstTrace firstHead; let tail ← firstTail; pure (head :: tail))
      (do let head ← Except.map secondTrace secondHead; let tail ← secondTail; pure (head :: tail)) := by
  cases firstHead <;> cases secondHead <;> simp only [StatementExecution.OfRunLessKnown] at head
  · subst head
    simp [Except.map, bind, Except.bind, StatementExecution.AlternativesLessKnown]
  · cases firstTail <;> cases secondTail <;>
      simp_all [Except.map, bind, Except.bind, pure, Except.pure, StatementExecution.AlternativesLessKnown,
        StatementExecution.LessKnownAll, StatementExecution.LessKnown, firstOf, secondOf]

/-- For every index, values, statement, resolution state, clock value and run, and two connections
where the first knows fewer counters and knows every counter that the statement reads: the further
executions of the run ({name}`StatementExecution.ofAlternatives`) are in the relation
{name}`StatementExecution.AlternativesLessKnown`. Proof sketch: induction on the alternatives, with
{name}`StatementExecution.ofRun_counters` for each, because the transition of each alternative on the
first state is related to its transition on the second ({name}`advanceRun_counters`). -/
theorem StatementExecution.ofAlternatives_counters (index : Nat) (parameters : List Value)
    {first second : Connection} (same : first.LessKnown second) (resolved : Resolved.Statement)
    (after : ResolveState) (value : Int) (run : StatementRun)
    (known : first.state.counters.firstUnknown resolved.counterReads = none) :
    StatementExecution.AlternativesLessKnown
      (StatementExecution.ofAlternatives index parameters first resolved after value run)
      (StatementExecution.ofAlternatives index parameters second resolved after value run) := by
  suffices ∀ alternatives : List StatementRun.Alternative,
      StatementExecution.AlternativesLessKnown
        (StatementExecution.ofAlternatives index parameters first resolved after value
          { run with alternatives := alternatives })
        (StatementExecution.ofAlternatives index parameters second resolved after value
          { run with alternatives := alternatives }) from this run.alternatives
  intro alternatives
  induction alternatives with
  | nil => exact trivial
  | cons alternative rest ih =>
    have head := StatementExecution.ofRun_counters parameters same resolved after value alternative.toRun known
      (advanceRun_counters index resolved alternative.toRun same.1)
    simp only [StatementExecution.ofAlternatives, List.mapM_cons] at ih ⊢
    revert head ih
    generalize StatementExecution.ofRun parameters first resolved after value alternative.toRun
      (advanceRun index resolved first.state alternative.toRun) = firstHead
    generalize StatementExecution.ofRun parameters second resolved after value alternative.toRun
      (advanceRun index resolved second.state alternative.toRun) = secondHead
    intro ih head
    exact StatementExecution.AlternativesLessKnown.cons head _ _ (fun _ => rfl) (fun _ => rfl) ih

end Belay.Sqlite.Model
