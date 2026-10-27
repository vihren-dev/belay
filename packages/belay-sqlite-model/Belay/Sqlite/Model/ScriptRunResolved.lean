import Belay.Sqlite.Model.ScriptRunSingleton
import Belay.Sqlite.Model.ScriptRunClock
import Belay.Sqlite.Model.StepCatalogLaws

set_option doc.verso true

/-! The trace of {name}`Belay.Sqlite.Model.runSqlFrom` and the resolution state of a step (ADR 0017, D3, amended
2026-10-22): the first part of the agreement of the new run with the old one, which
{lit}`Belay.Sqlite.Model.ScriptRunLaws` completes. -/

namespace Belay.Sqlite.Model

/-- What {name}`runSqlFrom` gives for each statement: the output of each statement that runs,
up to and including the first that halts, and the state after the last statement when no
statement halts. -/
structure SqlTrace where
  /-- The output of each statement that runs, from its transition ({name}`Output.ofStep`). -/
  outputs : List Output
  /-- The state after the last statement, or {lean}`(none : Option SqlState)` after a halt. -/
  final : Option SqlState

/-- The trace of {name}`runSqlFrom`: each statement advances with its values at its position
with {name}`advance` and gives {name}`Output.ofStep` of its run and its transition; a halt ends the trace. -/
def sqlTraceFrom (position : Nat) : List (Resolved.Statement × List Value) → SqlState → SqlTrace
  | [], state => { outputs := [], final := some state }
  | (statement, parameters) :: rest, state =>
    let output := Output.ofStep (state.clock position) parameters statement state
      (state.statementRun (state.clock position) parameters statement) (advance position statement parameters state)
    match advance position statement parameters state with
    | .halt _ => { outputs := [output], final := none }
    | .next next =>
      let later := sqlTraceFrom (position + 1) rest next
      { later with outputs := output :: later.outputs }

/-- For every position, script of statements with values, state and final state: if the trace
has the final state, then
{name}`runSqlFrom` gives the success or the pending transaction of {name}`SqlState.finish` of
that state. Proof sketch: induction on the script; a halt has no final state. -/
theorem sqlTraceFrom_final :
    ∀ (position : Nat) (script : List (Resolved.Statement × List Value)) (state final : SqlState),
    (sqlTraceFrom position script state).final = some final →
    runSqlFrom position script state = final.finish (.success final.database)
  | _, [], state, final, ended => by
    simp only [sqlTraceFrom, Option.some.injEq] at ended
    subst ended
    rfl
  | position, (statement, parameters) :: rest, state, final, ended => by
    simp only [sqlTraceFrom] at ended
    simp only [runSqlFrom]
    split at ended
    · cases ended
    · rename_i next continued
      rw [continued]
      exact sqlTraceFrom_final (position + 1) rest next final ended

/-- For every state and resolution state: if the state agrees with the resolution state
({name}`SqlState.Agrees`), the connection with the state and the resolution state's settings
has that resolution state. Proof sketch: the catalogs and the saved catalogs are equal by the
agreement, and the settings are the resolution state's; the structures are then equal field by
field. -/
theorem Connection.resolveState_of_agrees {state : SqlState} {target : ResolveState} (agrees : state.Agrees target) :
    ({ state, foreignKeys := target.foreignKeys, recursiveTriggers := target.recursiveTriggers } : Connection).resolveState = target := by
  obtain ⟨catalog, saved⟩ := agrees
  cases target
  simp_all [Connection.resolveState]

/-- For every context, optional clock, index, connection, statement, list of values, resolved
statement and resolution state: if the statement resolves against the connection's resolution
state, and the connection's clock assignment gives the statement's clock value
({name}`statementClock`) at the index when it has one, then the step of the run with the clock
and the values either ends, or continues with the output of {name}`Output.ofStep` with the
values of the run and the transition of {name}`advance` with the values (and some list of further executions), and the next connection is
{name}`Connection.afterStep` of that transition with the resolution state and the counts of the run. Proof
sketch: unfold the step with the resolution; a statement without a clock value, the support
check and an {name}`Output.unmodeled` end it; otherwise the clock value is the assignment's, so
the step's transition is {name}`advance` by definition, and its output and its next connection
are the stated ones. -/
theorem runScriptStep_resolved {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {resolved : Resolved.Statement} {after : ResolveState}
    (ok : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (fits : ∀ value, statementClock clock index resolved = some value → connection.state.clock index = value) :
    (∃ reason, runScriptStep context clock index connection statement parameters = .ended reason) ∨
    ∃ next others, runScriptStep context clock index connection statement parameters = .continued
        (Output.ofStep (connection.state.clock index) parameters resolved connection.state
          (connection.state.statementRun (connection.state.clock index) parameters resolved)
          (advance index resolved parameters connection.state)) next others ∧
      next = connection.afterStep after (connection.state.statementRun (connection.state.clock index) parameters resolved).counts
        (advance index resolved parameters connection.state) := by
  simp only [runScriptStep, runScriptStepWith, ranScriptStep, ok, Except.map]
  split
  · exact .inl ⟨_, rfl⟩
  · rename_i value valued
    obtain rfl := fits value valued
    split
    · exact .inl ⟨_, rfl⟩
    · split
      · exact .inl ⟨_, rfl⟩
      · split
        · exact .inl ⟨_, rfl⟩
        all_goals
          rename_i stepped
          have unfolded : advance index resolved parameters connection.state = advanceRun index resolved connection.state
              (connection.state.statementRun (connection.state.clock index) parameters resolved) := rfl
          rw [unfolded, stepped]
          split
          · exact .inl ⟨_, rfl⟩
          · exact .inr ⟨_, _, rfl, rfl⟩

end Belay.Sqlite.Model
