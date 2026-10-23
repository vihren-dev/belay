import Belay.Sqlite.Model.ScriptRunAppend

set_option doc.verso true

/-! A run does not depend on the counters of its connection while no statement reads them
(ADR 0024, D1). Two connections that differ at most in their counters take the same steps: the
same outputs, and next connections that again differ at most in their counters. -/

namespace Belay.Sqlite.Model

/-- Two states with the same database, snapshot and clock assignment; their counters can differ. -/
def SqlState.SameBesidesCounters (first second : SqlState) : Prop :=
  first.database = second.database ∧ first.snapshot = second.snapshot ∧ first.clock = second.clock

/-- Two transitions that agree besides the counters: both continue with states that are the same
besides their counters ({name}`SqlState.SameBesidesCounters`), or both halt with the same
outcome. -/
def SqlTransition.SameBesidesCounters : SqlTransition → SqlTransition → Prop
  | .next first, .next second => first.SameBesidesCounters second
  | .halt first, .halt second => first = second
  | .next _, .halt _ | .halt _, .next _ => False

/-- Two connections whose states are the same besides their counters and that have the same
settings. For example, a connection and the same connection after a write are not in this
relation when the write changed the database. -/
def Connection.SameBesidesCounters (first second : Connection) : Prop :=
  first.state.SameBesidesCounters second.state ∧ first.foreignKeys = second.foreignKeys ∧
    first.recursiveTriggers = second.recursiveTriggers

/-- For every statement-step result on two states that are the same besides their counters: the
transitions of {name}`advanceWith` for one effect agree besides the counters. Proof sketch: no case
reads the counters; split on the statement and the snapshot. -/
theorem advanceWith_counters (position : Nat) (statement : Resolved.Statement) (effect : Effect) {first second : SqlState}
    (same : first.SameBesidesCounters second) :
    (advanceWith position statement first effect).SameBesidesCounters (advanceWith position statement second effect) := by
  obtain ⟨database, snapshot, clockOf⟩ := same
  cases first
  cases second
  simp only at database snapshot clockOf
  subst database snapshot clockOf
  cases statement <;>
    first
    | (cases effect with
        | ok database => simp [advanceWith, SqlState.publish, SqlTransition.SameBesidesCounters, SqlState.SameBesidesCounters]
        | error failure =>
          obtain ⟨reason, reached⟩ := failure
          simp [advanceWith, SqlState.publish, SqlState.failed, SqlState.finish, SqlTransition.SameBesidesCounters])
    | (simp only [advanceWith]; split <;> simp [SqlState.finish, SqlTransition.SameBesidesCounters, SqlState.SameBesidesCounters])

/-- For every transition pair that agrees besides the counters and every counts: the transitions
after the counts ({name}`SqlTransition.counted`) agree besides the counters. Proof sketch: a halt
stays, and the counts change only the counters of a state. -/
theorem SqlTransition.counted_counters (counts : Counts) {first second : SqlTransition}
    (same : first.SameBesidesCounters second) :
    (first.counted counts).SameBesidesCounters (second.counted counts) := by
  cases first <;> cases second <;> simp_all [SqlTransition.counted, SqlTransition.SameBesidesCounters, SqlState.SameBesidesCounters]

/-- For every position, statement and run, and two states that are the same besides their
counters: the transitions of {name}`advanceRun` agree besides the counters. Proof sketch:
{name}`advanceWith_counters` and {name}`SqlTransition.counted_counters`. -/
theorem advanceRun_counters (position : Nat) (statement : Resolved.Statement) (run : StatementRun)
    {first second : SqlState} (same : first.SameBesidesCounters second) :
    (advanceRun position statement first run).SameBesidesCounters (advanceRun position statement second run) :=
  SqlTransition.counted_counters run.counts (advanceWith_counters position statement run.effect same)

/-- For every clock value, values, statement, run, two states that are the same besides their
counters, and two transitions that agree besides the counters: the outputs of
{name}`Output.ofStep` are equal. Proof sketch: the output reads the states only for their
database and the transitions only for whether they continue or how they halt. -/
theorem Output.ofStep_counters (clock : Int) (parameters : List Value) (statement : Resolved.Statement)
    (run : StatementRun) {first second : SqlState} {firstStep secondStep : SqlTransition}
    (same : first.SameBesidesCounters second) (steps : firstStep.SameBesidesCounters secondStep) :
    Output.ofStep clock parameters statement first run firstStep =
      Output.ofStep clock parameters statement second run secondStep := by
  obtain ⟨database, snapshot, clockOf⟩ := same
  cases first
  cases second
  simp only at database snapshot clockOf
  subst database snapshot clockOf
  cases firstStep <;> cases secondStep
  · cases statement <;> simp [Output.ofStep, statementOutput, possibleOutput, haltError]
  · exact absurd steps id
  · exact absurd steps id
  · simp only [SqlTransition.SameBesidesCounters] at steps
    subst steps
    rfl

/-- What a step of a run gives, besides the counters: both runs end for the same reason, or both
continue with the same output and with connections that are the same besides their counters. -/
def RunStep.SameBesidesCounters : RunStep → RunStep → Prop
  | .ended first, .ended second => first = second
  | .continued firstOutput first, .continued secondOutput second =>
    firstOutput = secondOutput ∧ first.SameBesidesCounters second
  | .ended _, .continued .. | .continued .., .ended _ => False

/-- For every connection pair that is the same besides the counters, every after-state, counts and
transition pair that agrees besides the counters: the connections after the step agree besides the
counters. Proof sketch: a transition that continues gives its state; a halt gives the database of
its outcome, which is the same on both sides. -/
theorem Connection.afterStep_counters {first second : Connection} (after : ResolveState) (counts : Counts)
    {firstStep secondStep : SqlTransition} (same : first.SameBesidesCounters second)
    (steps : firstStep.SameBesidesCounters secondStep) :
    (first.afterStep after counts firstStep).SameBesidesCounters (second.afterStep after counts secondStep) := by
  cases firstStep <;> cases secondStep
  · simp_all [Connection.afterStep, Connection.SameBesidesCounters, SqlTransition.SameBesidesCounters]
  · exact absurd steps id
  · exact absurd steps id
  · simp only [SqlTransition.SameBesidesCounters] at steps
    subst steps
    rename_i outcome
    cases outcome <;> simp_all [Connection.afterStep, Connection.afterError, Connection.SameBesidesCounters,
      SqlState.SameBesidesCounters]

/-- For every context, clock, index, statement and values, and two connections that are the same
besides their counters: the steps of {name}`runScriptStep` agree besides the counters. Proof sketch:
resolution, the clock value and the run read the database, the snapshot and the settings, which are
the same; the output and the next connection follow from {name}`Output.ofStep_counters`,
{name}`advanceRun_counters` and {name}`Connection.afterStep_counters`. -/
theorem runScriptStep_counters (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {first second : Connection} (same : first.SameBesidesCounters second) (statement : Syntax.Statement)
    (parameters : List Value) :
    (runScriptStep context clock index first statement parameters).SameBesidesCounters
      (runScriptStep context clock index second statement parameters) := by
  have resolving : first.resolveState = second.resolveState := by
    obtain ⟨⟨database, snapshot, _⟩, settings, recursive⟩ := same
    simp only [Connection.resolveState, database, snapshot, settings, recursive]
  have database := same.1.1
  unfold runScriptStep runScriptStepWith
  rw [resolving]
  cases resolveStatement context second.resolveState statement with
  | error restriction => simp [RunStep.SameBesidesCounters]
  | ok resolvedAfter =>
    obtain ⟨resolved, after⟩ := resolvedAfter
    simp only
    cases statementClock clock index resolved with
    | none => simp [RunStep.SameBesidesCounters]
    | some value =>
      simp only [database]
      by_cases ready : (runStatement value parameters resolved second.state.database).ready = true
      · have steps := advanceRun_counters index resolved (runStatement value parameters resolved second.state.database) same.1
        have output := Output.ofStep_counters value parameters resolved
          (runStatement value parameters resolved second.state.database) same.1 steps
        simp only [ready, Bool.not_true, Bool.false_eq_true, ite_false, ranScriptStep, output]
        split
        · simp [RunStep.SameBesidesCounters]
        all_goals
          simp only [RunStep.SameBesidesCounters]
          exact ⟨trivial, Connection.afterStep_counters after _ same steps⟩
      · simp [ready, RunStep.SameBesidesCounters]

/-- For every context, clock, statements with values, and two connections that are the same besides
their counters: the runs ({name}`runScriptFrom`) have the same outputs, and end on connections that
are the same besides their counters. Proof sketch: induction on the statements, with
{name}`runScriptStep_counters` for each step. -/
theorem runScriptFrom_counters (context : ResolveContext) (clock : Option Clock) :
    ∀ (script : List (Syntax.Statement × List Value)) (index : Nat) {first second : Connection},
      first.SameBesidesCounters second →
        (runScriptFrom context clock index first script).outputs =
            (runScriptFrom context clock index second script).outputs ∧
          (runScriptFrom context clock index first script).connection.SameBesidesCounters
            (runScriptFrom context clock index second script).connection
  | [], _, _, _, same => ⟨rfl, same⟩
  | (statement, parameters) :: rest, index, first, second, same => by
    have step := runScriptStep_counters context clock index same statement parameters
    unfold runScriptFrom
    cases firstStep : runScriptStep context clock index first statement parameters with
    | ended reason =>
      cases secondStep : runScriptStep context clock index second statement parameters with
      | ended other =>
        rw [firstStep, secondStep] at step
        simp only [RunStep.SameBesidesCounters] at step
        subst step
        exact ⟨rfl, same⟩
      | continued output next => rw [firstStep, secondStep] at step; exact absurd step id
    | continued output next =>
      cases secondStep : runScriptStep context clock index second statement parameters with
      | ended other => rw [firstStep, secondStep] at step; exact absurd step id
      | continued otherOutput otherNext =>
        rw [firstStep, secondStep] at step
        obtain ⟨sameOutput, sameNext⟩ := step
        subst sameOutput
        have later := runScriptFrom_counters context clock rest (index + 1) sameNext
        exact ⟨by simp only [later.1], later.2⟩

end Belay.Sqlite.Model
