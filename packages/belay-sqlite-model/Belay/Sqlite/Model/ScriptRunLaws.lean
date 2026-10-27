import Belay.Sqlite.Model.ScriptRunResolved

set_option doc.verso true

/-! The run that continues after an error agrees with {name}`Belay.Sqlite.Model.runSqlFrom`
(ADR 0017, D3, amended 2026-10-22). For a script that resolution accepts, on a state whose
clock assignment fits the run's clock ({name}`Belay.Sqlite.Model.ClockFits`), the two runs give
the same output for each statement up to and including the first error, and the same state at
the end of a script without an error, unless the new run ends earlier at a statement that the
model does not describe. {lit}`ScriptRunStates.lean` adds the state before each statement and the
database after the first error. -/

namespace Belay.Sqlite.Model

/-- For every context, connection, statement, list of values, resolved statement, resolution
state and state: if the statement resolves against the connection's resolution state to the
resolution state {lit}`after`, and {name}`advance` with the values continues with the state, then the connection with the state
and the settings of {lit}`after` has the resolution state {lit}`after`. Proof sketch: the
transition keeps the state in agreement with the resolution ({name}`advance_agrees`,
{name}`resolveStatement_after`), and {name}`Connection.resolveState_of_agrees` applies. -/
theorem Connection.resolveState_after_next {context : ResolveContext} {index : Nat} {connection : Connection}
    {statement : Syntax.Statement} {resolved : Resolved.Statement} {after : ResolveState} {state : SqlState}
    (ok : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    {parameters : List Value} (advanced : advance index resolved parameters connection.state = .next state) :
    ({ state, foreignKeys := after.foreignKeys, recursiveTriggers := after.recursiveTriggers } : Connection).resolveState = after := by
  have agrees := advance_agrees (state := connection.resolveState) ⟨rfl, rfl⟩ advanced
  rw [← resolveStatement_after context _ _ statement resolved ok] at agrees
  exact Connection.resolveState_of_agrees agrees

/-- The agreement of the two runs (ADR 0017, D3). For every context, optional clock, script of
statements with values, index, connection, resolved statements and final resolution state: if
{name}`resolveFrom` resolves the statements of the script from the index against the
connection's resolution state with the resolved statements, and the clock assignment of the
connection's state fits the run with the clock from the index over the resolved statements
({name}`ClockFits`), then one of the following holds for {name}`runScriptFrom` of the script
with the clock and the trace of {name}`runSqlFrom` of the resolved statements, each with the
values of its statement in the script ({name}`bindValues`), on the connection's state
({name}`sqlTraceFrom`):

* the run ends early: its outputs are some outputs and then one {name}`Output.unmodeled`, and
  those outputs are a prefix of the trace's outputs;
* the run does not end early before the first error: its outputs are the trace's outputs and
  then more outputs; when the trace has a final state (no statement halts), there are no more
  outputs and the run's connection has that state.

The statement says nothing about the outputs after the first error, which the trace does not
have. From index 0, the clock assignment of {name}`scriptClock` fits the run with its
assignment and the run without a clock ({name}`ClockFits.scriptClock`), so the trace is that of
{name}`runSqlAt`. Proof sketch: induction on the script. Each step resolves against the
connection's resolution state and runs at the assignment's clock value ({name}`ClockFits.head`);
a step that continues keeps the states in agreement ({name}`advance_agrees`) and the clock
assignment ({name}`advance_clock`), so the next statement resolves against the state that
{name}`resolveFrom` gives ({name}`resolveStatement_after`) and the rest fits
({name}`ClockFits.tail`). -/
theorem runScriptFrom_agrees (context : ResolveContext) (clock : Option Clock) :
    ∀ (script : List (Syntax.Statement × List Value)) (index : Nat) (connection : Connection)
      (resolved : List Resolved.Statement) (final : ResolveState),
      resolveFrom context index connection.resolveState (script.map (·.1)) = .ok (resolved, final) →
      ClockFits clock index resolved connection.state.clock →
      (∃ before reason, (runScriptFrom context clock index connection script).outputs = before ++ [.unmodeled reason] ∧
        before <+: (sqlTraceFrom index (bindValues resolved (script.map (·.2))) connection.state).outputs) ∨
      (∃ later, (runScriptFrom context clock index connection script).outputs =
          (sqlTraceFrom index (bindValues resolved (script.map (·.2))) connection.state).outputs ++ later ∧
        ∀ state, (sqlTraceFrom index (bindValues resolved (script.map (·.2))) connection.state).final = some state →
          later = [] ∧ (runScriptFrom context clock index connection script).connection.state = state)
  | [], index, connection, resolved, final, ok, _ => by
    simp only [List.map_nil, resolveFrom, Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨rfl, rfl⟩ := ok
    refine .inr ⟨[], ?_, fun state ended => ?_⟩
    · rfl
    · simp only [bindValues, sqlTraceFrom, Option.some.injEq] at ended
      exact ⟨rfl, ended⟩
  | (statement, parameters) :: rest, index, connection, resolved, final, ok, fits => by
    simp only [List.map_cons, resolveFrom, bind, Except.bind] at ok
    split at ok
    · cases ok
    · rename_i head headState headOk
      split at ok
      · cases ok
      · rename_i later restOk
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
        obtain ⟨rfl, rfl⟩ := ok
        rcases runScriptStep_resolved (index := index) (parameters := parameters) headOk (fun _ => fits.head) with
          ⟨reason, ended⟩ | ⟨next, _, continued, afterStep⟩
        · refine .inl ⟨[], reason, ?_, List.nil_prefix⟩
          simp [runScriptFrom, ended]
        · simp only [List.map_cons, bindValues_cons_cons, runScriptFrom, continued, sqlTraceFrom]
          split
          · exact .inr ⟨_, rfl, fun _ ended => by cases ended⟩
          · rename_i state advanced
            have nextState : next = { state, foreignKeys := headState.foreignKeys, recursiveTriggers := headState.recursiveTriggers } := by
              rw [afterStep, advanced]; rfl
            rw [← Connection.resolveState_after_next headOk advanced, ← nextState] at restOk
            rw [nextState] at restOk ⊢
            have restFits : ClockFits clock (index + 1) later.1 state.clock := by
              rw [advance_clock advanced]; exact fits.tail
            rcases runScriptFrom_agrees context clock rest (index + 1) _ later.1 later.2 restOk restFits with
              ⟨before, reason, outputs, isPrefix⟩ | ⟨more, outputs, ending⟩
            · exact .inl ⟨_ :: before, reason, by simp [outputs], List.cons_prefix_cons.mpr ⟨rfl, isPrefix⟩⟩
            · exact .inr ⟨more, by simp [outputs], ending⟩

end Belay.Sqlite.Model
