import Belay.Sqlite.Model.ScriptRunLaws

set_option doc.verso true

/-! The states of the run that continues after an error agree with those of
{name}`Belay.Sqlite.Model.runSqlFrom` (ADR 0017, D3, amended 2026-10-22). For a script that
resolution accepts, the run has the same state as {name}`Belay.Sqlite.Model.runSqlFrom` before
each statement up to the first error, and the same database after the first error, unless the
run ends earlier at a statement that the model does not describe. The outputs agree by
{name}`Belay.Sqlite.Model.runScriptFrom_agrees`. -/

namespace Belay.Sqlite.Model

/-- The states of {name}`runSqlFrom`: the state before each statement that it reaches and, when
no statement halts, the state at the end; and the outcome of the statement that halts, when one
does. For example, a script of one statement that halts with an outcome gives the state before
it and the outcome. -/
def sqlStatesFrom (position : Nat) : List Resolved.Statement → SqlState → List SqlState × Option Outcome
  | [], state => ([state], none)
  | statement :: rest, state => match advance position statement state with
    | .halt outcome => ([state], some outcome)
    | .next next =>
      let later := sqlStatesFrom (position + 1) rest next
      (state :: later.1, later.2)

/-- For every position, script and state: the first state of {name}`sqlStatesFrom` is the state.
Proof sketch: by cases on the script and on the transition. -/
theorem sqlStatesFrom_head (position : Nat) (script : List Resolved.Statement) (state : SqlState) :
    (sqlStatesFrom position script state).1[0]? = some state := by
  cases script with
  | nil => rfl
  | cons statement rest =>
    simp only [sqlStatesFrom]
    split <;> rfl

/-- For every connection, setting and outcome: the database of the connection after the
outcome ({name}`Connection.afterError`) is the outcome's database ({name}`Outcome.database`).
Proof sketch: for each constructor of the outcome, both sides are the same database by
definition. -/
theorem Connection.afterError_database (connection : Connection) (foreignKeys : Bool) (outcome : Outcome) :
    (connection.afterError foreignKeys outcome).state.database = outcome.database := by
  cases outcome <;> rfl

/-- For every context, script, index, connection, resolved statements, final resolution state,
count and state: if {name}`resolveFrom` resolves the script from the index against the
connection's resolution state with the resolved statements, the run of the first {lit}`count`
statements gives no {name}`Output.unmodeled`, and the state at position {lit}`count` of
{name}`sqlStatesFrom` of the resolved statements on the connection's state is the state, then
the connection after that run has the state. So the run and {name}`runSqlFrom` have the same
state before each statement up to and including the first that halts, and at the end when no
statement halts. Proof sketch: induction on the script; each step that continues keeps the
connection's resolution state equal to the next resolution state
({name}`Connection.resolveState_after_next`), and a step that halts has no later state. -/
theorem runScriptFrom_states (context : ResolveContext) :
    ∀ (script : List Syntax.Statement) (index : Nat) (connection : Connection) (resolved : List Resolved.Statement)
      (final : ResolveState) (count : Nat) (state : SqlState),
      resolveFrom context index connection.resolveState script = .ok (resolved, final) →
      (runScriptFrom context index connection (script.take count)).outputs.all (!·.endsRun) = true →
      (sqlStatesFrom index resolved connection.state).1[count]? = some state →
      (runScriptFrom context index connection (script.take count)).connection.state = state
  | script, index, connection, resolved, final, 0, state, _, _, found => by
    rw [sqlStatesFrom_head, Option.some.injEq] at found
    simp [runScriptFrom, found]
  | [], index, connection, resolved, final, count + 1, state, ok, _, found => by
    simp only [resolveFrom, Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨rfl, rfl⟩ := ok
    simp [sqlStatesFrom] at found
  | statement :: rest, index, connection, resolved, final, count + 1, state, ok, running, found => by
    simp only [resolveFrom, bind, Except.bind] at ok
    split at ok
    · cases ok
    · rename_i head headState headOk
      split at ok
      · cases ok
      · rename_i later restOk
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
        obtain ⟨rfl, rfl⟩ := ok
        rcases runScriptStep_resolved (index := index) headOk with ⟨reason, ended⟩ | ⟨next, continued, afterStep⟩
        · simp [runScriptFrom, ended, Output.endsRun] at running
        · simp only [List.take_succ_cons, runScriptFrom, continued, List.all_cons] at running ⊢
          simp only [sqlStatesFrom] at found
          split at found
          · simp at found
          · rename_i nextState advanced
            have nextIs : next = { state := nextState, foreignKeys := headState.foreignKeys } := by
              rw [afterStep, advanced]; rfl
            rw [← Connection.resolveState_after_next headOk advanced, ← nextIs] at restOk
            simp only [List.getElem?_cons_succ] at found
            rw [show nextState = next.state by rw [nextIs]] at found
            rw [Bool.and_eq_true] at running
            exact runScriptFrom_states context rest (index + 1) next later.1 later.2 count state restOk
              running.2 found

/-- For every context, script, index, connection, resolved statements, final resolution state
and outcome: if {name}`resolveFrom` resolves the script as in {name}`runScriptFrom_states`, a
statement of {name}`runSqlFrom` halts with the outcome ({name}`sqlStatesFrom`), and the run up
to and including that statement gives no {name}`Output.unmodeled`, then the database of the
connection after that run is the outcome's database. So the two runs have the same database after
the first error. Proof sketch: induction on the script; at the statement that halts, the
connection after it is {name}`Connection.afterError` of the outcome
({name}`Connection.afterError_database`). -/
theorem runScriptFrom_halt_database (context : ResolveContext) :
    ∀ (script : List Syntax.Statement) (index : Nat) (connection : Connection) (resolved : List Resolved.Statement)
      (final : ResolveState) (outcome : Outcome),
      resolveFrom context index connection.resolveState script = .ok (resolved, final) →
      (sqlStatesFrom index resolved connection.state).2 = some outcome →
      (runScriptFrom context index connection
        (script.take (sqlStatesFrom index resolved connection.state).1.length)).outputs.all (!·.endsRun) = true →
      (runScriptFrom context index connection
        (script.take (sqlStatesFrom index resolved connection.state).1.length)).connection.state.database =
          outcome.database
  | [], index, connection, resolved, final, outcome, ok, halted, _ => by
    simp only [resolveFrom, Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨rfl, rfl⟩ := ok
    simp [sqlStatesFrom] at halted
  | statement :: rest, index, connection, resolved, final, outcome, ok, halted, running => by
    simp only [resolveFrom, bind, Except.bind] at ok
    split at ok
    · cases ok
    · rename_i head headState headOk
      split at ok
      · cases ok
      · rename_i later restOk
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
        obtain ⟨rfl, rfl⟩ := ok
        rcases runScriptStep_resolved (index := index) headOk with ⟨reason, ended⟩ | ⟨next, continued, afterStep⟩
        · simp only [sqlStatesFrom] at running
          split at running <;> simp [runScriptFrom, ended, Output.endsRun] at running
        · cases advanced : advance index head connection.state with
          | halt stopped =>
            simp only [sqlStatesFrom, advanced, Option.some.injEq] at halted ⊢
            subst halted
            simp only [List.length_singleton, List.take_succ_cons, List.take_zero, runScriptFrom, continued]
            rw [afterStep, advanced]
            exact Connection.afterError_database _ _ _
          | next nextState =>
            have nextIs : next = { state := nextState, foreignKeys := headState.foreignKeys } := by
              rw [afterStep, advanced]; rfl
            rw [← Connection.resolveState_after_next headOk advanced, ← nextIs] at restOk
            simp only [sqlStatesFrom, advanced] at halted running ⊢
            simp only [List.length_cons, List.take_succ_cons, runScriptFrom, continued, List.all_cons,
              Bool.and_eq_true] at running ⊢
            rw [show nextState = next.state by rw [nextIs]] at halted running ⊢
            exact runScriptFrom_halt_database context rest (index + 1) next later.1 later.2 outcome restOk halted
              running.2

end Belay.Sqlite.Model
