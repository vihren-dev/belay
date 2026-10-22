import Belay.Sqlite.Model.ScriptRun
import Belay.Sqlite.Model.StepCatalogLaws
import Belay.Sqlite.Model.Resolution.ResolveStateSpec

set_option doc.verso true

/-! The run that continues after an error agrees with {name}`Belay.Sqlite.Model.runSqlFrom`
(ADR 0017, D3, amended 2026-10-22). For a script that resolution accepts, the two runs give the
same output for each statement up to and including the first error, and the same state at the
end of a script without an error, unless the new run ends earlier at a statement that the model
does not describe. -/

namespace Belay.Sqlite.Model

/-- What {name}`runSqlFrom` gives for each statement: the output of each statement that runs,
up to and including the first that halts, and the state after the last statement when no
statement halts. -/
structure SqlTrace where
  /-- The output of each statement that runs, from its transition ({name}`Output.ofStep`). -/
  outputs : List Output
  /-- The state after the last statement, or {lean}`(none : Option SqlState)` after a halt. -/
  final : Option SqlState

/-- The trace of {name}`runSqlFrom`: each statement advances at its position with
{name}`advance` and gives {name}`Output.ofStep` of its transition; a halt ends the trace. -/
def sqlTraceFrom (position : Nat) : List Resolved.Statement → SqlState → SqlTrace
  | [], state => { outputs := [], final := some state }
  | statement :: rest, state =>
    let output := Output.ofStep (state.clock position) statement state (advance position statement state)
    match advance position statement state with
    | .halt _ => { outputs := [output], final := none }
    | .next next =>
      let later := sqlTraceFrom (position + 1) rest next
      { later with outputs := output :: later.outputs }

/-- For every position, script, state and final state: if the trace has the final state, then
{name}`runSqlFrom` gives the success or the pending transaction of {name}`SqlState.finish` of
that state. Proof sketch: induction on the script; a halt has no final state. -/
theorem sqlTraceFrom_final : ∀ (position : Nat) (script : List Resolved.Statement) (state final : SqlState),
    (sqlTraceFrom position script state).final = some final →
    runSqlFrom position script state = final.finish (.success final.database)
  | _, [], state, final, ended => by
    simp only [sqlTraceFrom, Option.some.injEq] at ended
    subst ended
    rfl
  | position, statement :: rest, state, final, ended => by
    simp only [sqlTraceFrom] at ended
    simp only [runSqlFrom]
    split at ended
    · cases ended
    · rename_i next continued
      rw [continued]
      exact sqlTraceFrom_final (position + 1) rest next final ended

/-- For every state and resolution state: if the state agrees with the resolution state
({name}`SqlState.Agrees`), the connection with the state and the resolution state's setting
has that resolution state. Proof sketch: the catalogs and the saved catalogs are equal by the
agreement, and the setting is the resolution state's; the structures are then equal field by
field. -/
theorem Connection.resolveState_of_agrees {state : SqlState} {target : ResolveState} (agrees : state.Agrees target) :
    ({ state, foreignKeys := target.foreignKeys } : Connection).resolveState = target := by
  obtain ⟨catalog, saved⟩ := agrees
  cases target
  simp_all [Connection.resolveState]

/-- For every context, index, connection, statement, resolved statement and resolution state:
if the statement resolves against the connection's resolution state, then the step of the run
either ends, or continues with the output of {name}`Output.ofStep` of the transition of
{name}`advance`, and when that transition continues with a state, the next connection has that
state and the resolution state's setting. Proof sketch: unfold the step with the resolution;
the clock, the support check and an {name}`Output.unmodeled` end it, and otherwise the step's
transition is {name}`advance` by definition, so its output and its next connection are the
stated ones. -/
theorem runScriptStep_resolved {context : ResolveContext} {index : Nat} {connection : Connection}
    {statement : Syntax.Statement} {resolved : Resolved.Statement} {after : ResolveState}
    (ok : resolveStatement context connection.resolveState statement = .ok (resolved, after)) :
    (∃ reason, runScriptStep context index connection statement = .ended reason) ∨
    ∃ next, runScriptStep context index connection statement = .continued
        (Output.ofStep (connection.state.clock index) resolved connection.state
          (advance index resolved connection.state)) next ∧
      ∀ state, advance index resolved connection.state = .next state →
        next = { state, foreignKeys := after.foreignKeys } := by
  simp only [runScriptStep, ok]
  split
  · exact .inl ⟨_, rfl⟩
  · split
    · exact .inl ⟨_, rfl⟩
    · split
      · exact .inl ⟨_, rfl⟩
      all_goals
        rename_i stepped
        have unfolded : advance index resolved connection.state = advanceWith index resolved connection.state
            (runStatement (connection.state.clock index) resolved connection.state.database).effect := rfl
        rw [unfolded, stepped]
        refine .inr ⟨_, rfl, fun state continued => ?_⟩
        simp only [continued, Connection.afterStep]

/-- The agreement of the two runs (ADR 0017, D3). For every context, script, index, connection,
resolved statements and final resolution state: if {name}`resolveFrom` resolves the script from
the index against the connection's resolution state with the resolved statements, then one of
the following holds for {name}`runScriptFrom` and the trace of {name}`runSqlFrom` of the
resolved statements on the connection's state ({name}`sqlTraceFrom`):

* the run ends early: its outputs are some outputs and then one {name}`Output.unmodeled`, and
  those outputs are a prefix of the trace's outputs;
* the run does not end early before the first error: its outputs are the trace's outputs and
  then more outputs; when the trace has a final state (no statement halts), there are no more
  outputs and the run's connection has that state.

The statement says nothing about the outputs after the first error, which the trace does not
have. Proof sketch: induction on the script. Each step resolves against the connection's
resolution state; a step that continues keeps the states in agreement ({name}`advance_agrees`),
so the next statement resolves against the state that {name}`resolveFrom` gives
({name}`resolveStatement_after`). -/
theorem runScriptFrom_agrees (context : ResolveContext) :
    ∀ (script : List Syntax.Statement) (index : Nat) (connection : Connection) (resolved : List Resolved.Statement)
      (final : ResolveState),
      resolveFrom context index connection.resolveState script = .ok (resolved, final) →
      (∃ before reason, (runScriptFrom context index connection script).outputs = before ++ [.unmodeled reason] ∧
        before <+: (sqlTraceFrom index resolved connection.state).outputs) ∨
      (∃ later, (runScriptFrom context index connection script).outputs =
          (sqlTraceFrom index resolved connection.state).outputs ++ later ∧
        ∀ state, (sqlTraceFrom index resolved connection.state).final = some state →
          later = [] ∧ (runScriptFrom context index connection script).connection.state = state)
  | [], index, connection, resolved, final, ok => by
    simp only [resolveFrom, Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨rfl, rfl⟩ := ok
    refine .inr ⟨[], ?_, fun state ended => ?_⟩
    · rfl
    · simp only [sqlTraceFrom, Option.some.injEq] at ended
      exact ⟨rfl, ended⟩
  | statement :: rest, index, connection, resolved, final, ok => by
    simp only [resolveFrom, bind, Except.bind] at ok
    split at ok
    · cases ok
    · rename_i head headState headOk
      split at ok
      · cases ok
      · rename_i later restOk
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
        obtain ⟨rfl, rfl⟩ := ok
        rcases runScriptStep_resolved (index := index) headOk with ⟨reason, ended⟩ | ⟨next, continued, nextState⟩
        · refine .inl ⟨[], reason, ?_, List.nil_prefix⟩
          simp [runScriptFrom, ended]
        · simp only [runScriptFrom, continued, sqlTraceFrom]
          split
          · exact .inr ⟨_, rfl, fun _ ended => by cases ended⟩
          · rename_i state advanced
            have agrees := advance_agrees (state := connection.resolveState) ⟨rfl, rfl⟩ advanced
            rw [← resolveStatement_after context _ _ statement head headOk] at agrees
            have resolves : next.resolveState = headState := by
              rw [nextState state advanced]
              exact Connection.resolveState_of_agrees agrees
            rw [← resolves] at restOk
            rw [nextState state advanced] at restOk ⊢
            rcases runScriptFrom_agrees context rest (index + 1) _ later.1 later.2 restOk with
              ⟨before, reason, outputs, isPrefix⟩ | ⟨more, outputs, ending⟩
            · exact .inl ⟨_ :: before, reason, by simp [outputs], List.cons_prefix_cons.mpr ⟨rfl, isPrefix⟩⟩
            · exact .inr ⟨more, by simp [outputs], ending⟩

end Belay.Sqlite.Model
