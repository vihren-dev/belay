import Belay.Sqlite.Model.KeysUniqueKeySteps
import Belay.Sqlite.Model.KeysUniqueTriggers
import Belay.Sqlite.Model.ForeignKeyRows

set_option doc.verso true

/-! The deletion of a row and the foreign-key actions keep the invariant of the row engine for
the atom "keys unique" (ADR 0022, D3, slice 2): a delete stores a sublist of the rows, and an
action is a nested write. -/

namespace Belay.Sqlite.Model

/-- For every catalog, run of the nested writes, link, action, position, old row, new row and
state: if the run keeps the invariant of the row engine from each state that satisfies
{name}`KeyState.KeysUnique`, and the state satisfies it, the result of {name}`runAction` keeps
the invariant (a success satisfies {name}`KeyState.KeysUnique` and a stop
{name}`KeyStop.KeysUnique`). Proof sketch: each branch keeps the state, fails without a state, or
is the nested run with the changed tables noted. -/
theorem runAction_keysUnique {catalog : Catalog} {run : RowWork → KeyState → Except KeyStop KeyState}
    (keeps : ∀ work state, state.KeysUnique catalog →
      ResultHolds (KeyState.KeysUnique catalog) (KeyStop.KeysUnique catalog) (run work state))
    (link : ForeignKeyLink) (action : Syntax.ForeignKeyAction) (position : Nat) (old : Row) (new : Option Row)
    {state : KeyState} (unique : state.KeysUnique catalog) :
    ResultHolds (KeyState.KeysUnique catalog) (KeyStop.KeysUnique catalog)
      (runAction catalog run link action position old new state) := by
  unfold runAction
  repeat' (first | split | dsimp only)
  all_goals first | exact unique | trivial | exact ResultHolds.map (keeps _ _ unique) fun _ reached => reached

/-- For every catalog, links, nested run, frame, position, flags, state and rowid: if the nested
run keeps the invariant ({name}`NestedRun.KeepsKeys`) and the state satisfies
{name}`KeyState.KeysUnique`, the result of {name}`deleteRow` keeps the invariant. Proof sketch:
the programs before and after the delete keep it ({name}`runPrograms_keysUnique`), the foreign-key
steps keep the rows ({name}`oldSteps_rows`), the delete stores a sublist of the rows
({name}`KeyState.keysUnique_changeRows_sublist`), and each action keeps it
({name}`runAction_keysUnique`). -/
theorem deleteRow_keysUnique {catalog : Catalog} {links : List ForeignKeyLink} {nested : NestedRun}
    (keeps : nested.KeepsKeys catalog) (frame : RowFrame) (position : Nat) (record ignore fire : Bool)
    {state : KeyState} (unique : state.KeysUnique catalog) (rowid : Int) :
    ResultHolds (KeyState.KeysUnique catalog) (KeyStop.KeysUnique catalog)
      (deleteRow catalog links nested frame position record ignore fire state rowid) := by
  unfold deleteRow
  split
  · dsimp only
    split <;> refine ResultHolds.bind (good := fun reached : KeyState × Bool => reached.1.KeysUnique catalog) ?_
      fun reached good => ?_
    all_goals first | exact runPrograms_keysUnique keeps _ _ _ _ _ unique | exact unique | skip
    all_goals
      obtain ⟨reachedState, ended⟩ := reached
      dsimp only
      split
      · exact good
      · split
        · refine ResultHolds.bind ((oldSteps_rows _ _ _ _ _ _ _).keysUnique_of_rows good) fun checked same => ?_
          have removed := KeyState.keysUnique_changeRows_sublist same (position := position)
            (change := fun rows => rows.filter (·.rowid != rowid)) fun rows => List.filter_sublist
          refine ResultHolds.bind (ResultHolds.foldlM (fun acted link good =>
            runAction_keysUnique (keeps frame.action) link _ position _ none good) _ _ removed) fun acted good => ?_
          first
            | exact good
            | exact ResultHolds.bind (runPrograms_keysUnique keeps _ _ _ _ _ good) fun _ reached => reached
        · exact good
  · exact unique
