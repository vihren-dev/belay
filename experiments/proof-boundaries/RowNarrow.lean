import Belay.Sqlite.Model.RowEngineResultLaws
import Belay.Sqlite.Model.TriggerRun

set_option doc.verso true

open Belay.Sqlite.Model

namespace ProofBoundaries

/-- A program preserves the success/stop predicates if entry has the stop contract and every
body step preserves them in the program's running frame. An ended row bypasses the suffix.
The proof checks entry and the WHEN condition, then folds the actual body once. -/
theorem programFromEffects {P : KeyState → Prop} {Q : KeyStop → Prop}
    (catalog : Catalog) (nested : NestedRun) (frame : RowFrame) (cells : List Value)
    (program : Resolved.Program) {state : KeyState} (good : P state)
    (entry : ResultHolds (fun _ : Unit => True) Q (enterProgram nested frame program.table state))
    (steps : ∀ step ∈ program.body, ∀ reached, P reached →
      ResultHolds (fun pair : KeyState × Bool => P pair.1) Q
        (runStep catalog nested { frame with running := program.trigger :: frame.running } cells reached step)) :
    ResultHolds (fun pair : KeyState × Bool => P pair.1) Q
      (runProgram catalog nested frame cells state program) := by
  unfold runProgram
  split
  · exact good
  · refine ResultHolds.bind entry fun _ _ => ?_
    split
    · exact good
    · refine ResultHolds.foldlM_mem _ (fun pair step member good => ?_) (state, false) good
      obtain ⟨reached, ended⟩ := pair
      dsimp only
      split
      · exact good
      · exact steps step member reached good

/-- A fired program sequence preserves the success/stop predicates if each fired program
does so from every good input. The proof folds the actual fired list and bypasses its suffix
after the row ends. It imposes no common representation on state or stop predicates. -/
theorem programsFromEffects {P : KeyState → Prop} {Q : KeyStop → Prop}
    (catalog : Catalog) (nested : NestedRun) (frame : RowFrame) (table : Nat)
    (time : Syntax.TriggerTime) (event : Resolved.TriggerEvent) (cells : List Value)
    (programs : ∀ program ∈ frame.fired table time event, ∀ state, P state →
      ResultHolds (fun pair : KeyState × Bool => P pair.1) Q (runProgram catalog nested frame cells state program))
    {state : KeyState} (good : P state) :
    ResultHolds (fun pair : KeyState × Bool => P pair.1) Q
      (runPrograms catalog nested frame table time event cells state) := by
  unfold runPrograms
  refine ResultHolds.foldlM_mem _ (fun pair program member good => ?_) (state, false) good
  obtain ⟨reached, ended⟩ := pair
  dsimp only
  split
  · exact good
  · exact programs program member reached good

#print axioms programFromEffects
#print axioms programsFromEffects

end ProofBoundaries
