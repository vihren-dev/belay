import Belay.Sqlite.Model.KeysUniqueKeyState
import Belay.Sqlite.Model.TriggerRun

set_option doc.verso true

/-! The trigger programs of a row keep the invariant of the row engine for the atom "keys
unique" (ADR 0022, D3, slice 2), when their nested writes keep it: a step of a program writes
only through the nested run, a SELECT and a {lit}`RAISE` keep the rows, and a FAIL or ROLLBACK
{lit}`RAISE` stops with the state. -/

namespace Belay.Sqlite.Model

/-- For the given catalog and nested run of the row engine: from every frame, work and state
that satisfies {name}`KeyState.KeysUnique`, the nested run holds the invariant: a success
satisfies {name}`KeyState.KeysUnique` and a stop {name}`KeyStop.KeysUnique`. -/
def NestedRun.KeepsKeys (catalog : Catalog) (nested : NestedRun) : Prop :=
  ∀ frame work state, state.KeysUnique catalog →
    ResultHolds (KeyState.KeysUnique catalog) (KeyStop.KeysUnique catalog) (nested frame work state)

/-- For the given catalog and result of a step of a program: a success has a state that
satisfies {name}`KeyState.KeysUnique`, whether or not the step ended the row, and a stop
satisfies {name}`KeyStop.KeysUnique`. -/
def ProgramResult.KeysUnique (catalog : Catalog) (result : Except KeyStop (KeyState × Bool)) : Prop :=
  ResultHolds (fun reached : KeyState × Bool => reached.1.KeysUnique catalog) (KeyStop.KeysUnique catalog) result

/-- For every catalog, state and kind of {lit}`RAISE`: if the state satisfies
{name}`KeyState.KeysUnique`, the result of {name}`raiseEffect` satisfies
{name}`ProgramResult.KeysUnique`. Proof sketch: IGNORE keeps the state, ABORT keeps no state,
and FAIL and ROLLBACK stop with the state. -/
theorem raiseEffect_keysUnique {catalog : Catalog} {state : KeyState} (unique : state.KeysUnique catalog)
    (kind : Syntax.RaiseKind) : ProgramResult.KeysUnique catalog (raiseEffect state kind) := by
  cases kind <;> first | exact unique | trivial

/-- For every catalog, nested run, frame, cells, state and step of a program: if the nested run
keeps the invariant ({name}`NestedRun.KeepsKeys`) and the state satisfies
{name}`KeyState.KeysUnique`, the result of {name}`runStep` satisfies
{name}`ProgramResult.KeysUnique`. Proof sketch: a write is the nested run, whose state
{name}`KeyState.afterStep` changes only in fields that the database does not read; a SELECT
keeps the rows or stops with an error; a {lit}`RAISE` is {name}`raiseEffect_keysUnique`. -/
theorem runStep_keysUnique {catalog : Catalog} {nested : NestedRun} (keeps : nested.KeepsKeys catalog)
    (frame : RowFrame) (cells : List Value) {state : KeyState} (unique : state.KeysUnique catalog)
    (step : Resolved.Step) : ProgramResult.KeysUnique catalog (runStep catalog nested frame cells state step) := by
  cases step with
  | raise filter arms otherwise =>
    simp only [runStep]
    split
    · exact raiseEffect_keysUnique unique _
    · exact unique
  | query query subqueries =>
    simp only [runStep]
    repeat' (first | split | dsimp only)
    all_goals first | trivial | exact unique
  | insert | update | delete =>
    simp only [runStep]
    unfold ProgramResult.KeysUnique
    split
    · exact ResultHolds.bind (keeps _ _ _ unique) fun _ reached => reached
    · trivial

/-- For every catalog, nested run, frame, table position and state: if the nested run keeps the
invariant ({name}`NestedRun.KeepsKeys`) and the state satisfies {name}`KeyState.KeysUnique`, the
result of {name}`enterProgram` is a success, which holds no property, or a stop that satisfies
{name}`KeyStop.KeysUnique`. Proof sketch: the result maps the result of the nested run of no rows,
which holds the invariant, and drops its state. -/
theorem enterProgram_keysUnique {catalog : Catalog} {nested : NestedRun} (keeps : nested.KeepsKeys catalog)
    (frame : RowFrame) (table : Nat) {state : KeyState} (unique : state.KeysUnique catalog) :
    ResultHolds (fun _ : Unit => True) (KeyStop.KeysUnique catalog) (enterProgram nested frame table state) :=
  ResultHolds.map (keeps frame (.delete table [] false false false) state unique) fun _ _ => trivial

/-- For every catalog, nested run, frame, cells, state and program: if the nested run keeps the
invariant ({name}`NestedRun.KeepsKeys`) and the state satisfies {name}`KeyState.KeysUnique`, the
result of {name}`runProgram` satisfies {name}`ProgramResult.KeysUnique`. Proof sketch: a program
that the frame runs already, with recursive triggers off, keeps the state; otherwise the entry of
the frame ({name}`enterProgram_keysUnique`) changes no state, a program whose condition is not
true keeps the state, and each step of the fold keeps the invariant ({name}`runStep_keysUnique`),
and a step after the end of the row keeps the state. -/
theorem runProgram_keysUnique {catalog : Catalog} {nested : NestedRun} (keeps : nested.KeepsKeys catalog)
    (frame : RowFrame) (cells : List Value) {state : KeyState} (unique : state.KeysUnique catalog)
    (program : Resolved.Program) : ProgramResult.KeysUnique catalog (runProgram catalog nested frame cells state program) := by
  unfold runProgram ProgramResult.KeysUnique
  split
  · exact unique
  · refine ResultHolds.bind (enterProgram_keysUnique keeps frame program.table unique) fun _ _ => ?_
    split
    · exact unique
    · refine ResultHolds.foldlM (good := fun reached : KeyState × Bool => reached.1.KeysUnique catalog)
        (fun reached step good => ?_) _ (state, false) unique
      obtain ⟨reachedState, ended⟩ := reached
      dsimp only
      split
      · exact good
      · exact runStep_keysUnique keeps _ cells good step

/-- For every catalog, nested run, frame, table, time, event, cells and state: if the nested run
keeps the invariant ({name}`NestedRun.KeepsKeys`) and the state satisfies
{name}`KeyState.KeysUnique`, the result of {name}`runPrograms` satisfies
{name}`ProgramResult.KeysUnique`. Proof sketch: a fold of {name}`runProgram_keysUnique`. -/
theorem runPrograms_keysUnique {catalog : Catalog} {nested : NestedRun} (keeps : nested.KeepsKeys catalog)
    (frame : RowFrame) (table : Nat) (time : Syntax.TriggerTime) (event : Resolved.TriggerEvent) (cells : List Value)
    {state : KeyState} (unique : state.KeysUnique catalog) :
    ProgramResult.KeysUnique catalog (runPrograms catalog nested frame table time event cells state) := by
  unfold runPrograms
  refine ResultHolds.foldlM (good := fun reached : KeyState × Bool => reached.1.KeysUnique catalog)
    (fun reached program good => ?_) _ (state, false) unique
  obtain ⟨reachedState, ended⟩ := reached
  dsimp only
  split
  · exact good
  · exact runProgram_keysUnique keeps frame cells good program

end Belay.Sqlite.Model
