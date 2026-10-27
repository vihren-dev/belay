import Belay.Sqlite.Model.ScriptRunSingleton

set_option doc.verso true

/-! The run of {lit}`ScriptRun.lean` does not depend on the index at which it starts, when the run has no clock or
a clock that gives the same value at every index: the part about the failure position. A failure position reaches
neither the output nor the connection after a statement ({name}`Belay.Sqlite.Model.Outcome.failure`). The
statement of the whole claim and the clock are in {lit}`Belay.Sqlite.Model.ScriptRunIndex`. -/

namespace Belay.Sqlite.Model

/-- The outcome with every failure position set to the position. -/
def Outcome.atPosition (position : Nat) : Outcome → Outcome
  | .success database => .success database
  | .failure _ reason database => .failure position reason database
  | .pending persisted visible error => .pending persisted visible (error.map fun (_, reason) => (position, reason))

/-- The transition with every failure position set to the position. -/
def SqlTransition.atPosition (position : Nat) : SqlTransition → SqlTransition
  | .next state => .next state
  | .halt outcome => .halt (outcome.atPosition position)

/-- For all positions, a statement, a state and an effect: the transition at the second position
is the transition at the first position with its failure positions set to the second. Proof
sketch: every failure that {name}`advanceWith` gives is at its position; case analysis on the
statement, the open transaction and the effect. -/
theorem advanceWith_atPosition (first second : Nat) (statement : Resolved.Statement) (state : SqlState)
    (effect : Effect) :
    advanceWith second statement state effect = (advanceWith first statement state effect).atPosition second := by
  cases statement <;> cases snapshot : state.snapshot <;> (try cases effect) <;>
    simp_all [advanceWith, SqlState.publish, SqlState.failed, SqlState.finish, SqlTransition.atPosition,
      Outcome.atPosition] <;> split <;> simp_all

/-- For every position and transition, the error of a halt ({name}`haltError`) is the same with
the failure positions set to the position. Proof sketch: case analysis on the transition and its
outcome; {name}`haltError` reads the reason of a failure, never its position. -/
@[simp] theorem haltError_atPosition (position : Nat) (transition : SqlTransition) :
    haltError (transition.atPosition position) = haltError transition := by
  cases transition with
  | next _ => rfl
  | halt outcome => cases outcome with
    | success _ => rfl
    | failure _ _ _ => rfl
    | pending _ _ error => cases error <;> rfl

/-- For every position and transition without a halt error ({name}`haltError`), setting the
failure positions does not change the transition: it has none. -/
theorem SqlTransition.atPosition_of_haltError (position : Nat) {transition : SqlTransition}
    (none : haltError transition = none) : transition.atPosition position = transition := by
  cases transition with
  | next _ => rfl
  | halt outcome => cases outcome with
    | success _ => rfl
    | failure _ _ _ => simp [haltError] at none
    | pending _ _ error => cases error <;> simp_all [haltError, SqlTransition.atPosition, Outcome.atPosition]

/-- For every clock value, list of values, statement, state, run, position and transition, the
output of the step ({name}`Output.ofStep`) is the same with the failure positions set to the position. Proof sketch:
with a halt error, the output reads only the error ({name}`haltError_atPosition`); without one,
the transition has no failure position ({name}`SqlTransition.atPosition_of_haltError`). -/
@[simp] theorem Output.ofStep_atPosition (clock : Int) (parameters : List Value) (statement : Resolved.Statement)
    (before : SqlState) (run : StatementRun) (position : Nat) (transition : SqlTransition) :
    Output.ofStep clock parameters statement before run (transition.atPosition position) =
      Output.ofStep clock parameters statement before run transition := by
  cases error : haltError transition with
  | none => rw [SqlTransition.atPosition_of_haltError position error]
  | some failure => simp only [Output.ofStep, haltError_atPosition, error]; cases failure <;> rfl

/-- For every connection, resolution state, counts, position and transition, the connection after the step
({name}`Connection.afterStep`) is the same with the failure positions set to the position: it
reads no failure position. -/
@[simp] theorem Connection.afterStep_atPosition (connection : Connection) (after : ResolveState) (counts : Counts)
    (position : Nat) (transition : SqlTransition) :
    connection.afterStep after counts (transition.atPosition position) = connection.afterStep after counts transition := by
  cases transition with
  | next _ => rfl
  | halt outcome => cases outcome <;> rfl

/-- For every counts, position and transition, applying the counts and setting the failure
positions to the position commute. Proof sketch: case analysis on the transition. -/
theorem SqlTransition.counted_atPosition (counts : Counts) (position : Nat) (transition : SqlTransition) :
    (transition.atPosition position).counted counts = (transition.counted counts).atPosition position := by
  cases transition <;> rfl

/-- For all positions, a statement, a state and a run: the transition after the run at the second
position is the transition at the first position with its failure positions set to the second.
Proof sketch: {name}`advanceWith_atPosition`, and the counts commute with the failure positions
({name}`SqlTransition.counted_atPosition`). -/
theorem advanceRun_atPosition (first second : Nat) (statement : Resolved.Statement) (state : SqlState)
    (run : StatementRun) :
    advanceRun second statement state run = (advanceRun first statement state run).atPosition second := by
  simp only [advanceRun, advanceWith_atPosition first second, SqlTransition.counted_atPosition]

/-- For every function that can fail, function on its results and list of arguments, mapping the results of
the monadic map is the monadic map of the mapped function. Proof sketch: induction on the arguments. -/
theorem List.mapM_except_map {α β γ : Type} (f : α → Except String β) (g : β → γ) :
    ∀ arguments : List α, (arguments.mapM f).map (List.map g) = arguments.mapM fun argument => (f argument).map g
  | [] => rfl
  | argument :: rest => by
    have later := List.mapM_except_map f g rest
    simp only [List.mapM_cons]
    cases first : f argument with
    | error reason => simp [first, bind, Except.bind, Except.map]
    | ok head =>
      cases others : rest.mapM f with
      | error reason =>
        rw [others] at later
        simp only [Except.map] at later ⊢
        simp [first, bind, Except.bind, Except.map, ← later]
      | ok tail =>
        rw [others] at later
        simp only [Except.map] at later ⊢
        simp [first, bind, Except.bind, Except.map, ← later, pure, Except.pure]

/-- For every two indexes, values, connection, resolved statement, resolution state, clock value and run, the
executions of the alternatives of the run ({name}`StatementExecution.ofAlternatives`) are the same at both
indexes: the index reaches an execution only through the position of a failure, which neither its output
nor its connection reads. Proof sketch: the execution of each alternative is the same at both indexes
({name}`advanceRun_atPosition`, {name}`Output.ofStep_atPosition`, {name}`Connection.afterStep_atPosition`),
and the map commutes with the executions ({name}`List.mapM_except_map`). -/
theorem StatementExecution.ofAlternatives_index (first second : Nat) (parameters : List Value) (connection : Connection)
    (resolved : Resolved.Statement) (after : ResolveState) (value : Int) (run : StatementRun) :
    (StatementExecution.ofAlternatives first parameters connection resolved after value run).map
        (List.map StatementExecution.Traced.execution) =
      (StatementExecution.ofAlternatives second parameters connection resolved after value run).map
        (List.map StatementExecution.Traced.execution) := by
  unfold StatementExecution.ofAlternatives
  rw [List.mapM_except_map, List.mapM_except_map]
  congr 1
  funext alternative
  have same : StatementExecution.ofRun parameters connection resolved after value alternative.toRun
      (advanceRun second resolved connection.state alternative.toRun) =
      StatementExecution.ofRun parameters connection resolved after value alternative.toRun
        (advanceRun first resolved connection.state alternative.toRun) := by
    rw [advanceRun_atPosition first second]
    simp [StatementExecution.ofRun]
  cases h : StatementExecution.ofRun parameters connection resolved after value alternative.toRun
      (advanceRun first resolved connection.state alternative.toRun) <;>
    simp_all [Except.map]

/-- For every optional clock, two indexes and resolved statement: if the clock, when the run
has one, gives the same value at both indexes, the statement's clock value
({name}`statementClock`) is the same at both. Proof sketch: case analysis on the clock; without
one, the value does not depend on the index. -/
theorem statementClock_index {clock : Option Clock} {first second : Nat}
    (same : ∀ assignment ∈ clock, assignment first = assignment second) (statement : Resolved.Statement) :
    statementClock clock first statement = statementClock clock second statement := by
  cases clock <;> simp_all [statementClock]

/-- For every context, optional clock, two indexes, connection, statement and list of values:
if the clock, when the run has one, gives the same value at both indexes, the statement's step
with the values ({name}`runScriptStep`) is the same at both. Proof sketch: resolution takes no
index, and the clock value is the same ({name}`statementClock_index`); the step at the first
index is the step at the second with its failure positions set ({name}`advanceWith_atPosition`),
and neither the output nor the next connection reads a failure position. -/
theorem runScriptStep_index (context : ResolveContext) (clock : Option Clock) (first second : Nat)
    (connection : Connection) (statement : Syntax.Statement) (parameters : List Value)
    (same : ∀ assignment ∈ clock, assignment first = assignment second) :
    runScriptStep context clock first connection statement parameters =
      runScriptStep context clock second connection statement parameters := by
  simp only [runScriptStep, runScriptStepWith, ranScriptStep, statementClock_index same, advanceRun_atPosition second first, Output.ofStep_atPosition,
    Connection.afterStep_atPosition, StatementExecution.ofAlternatives_index first second]

end Belay.Sqlite.Model
