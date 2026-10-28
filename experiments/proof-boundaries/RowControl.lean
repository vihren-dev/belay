import RowContract

set_option doc.verso true

open Belay.Sqlite.Model

namespace ProofBoundaries

/-- A trigger step preserves the state/stop contract when each nested write it generates is
permitted. The proof inspects the step once: nested writes use their contract and bookkeeping
closure, queries use error and bookkeeping facts, and RAISE uses its actual stop kind. -/
theorem rowStep {P Q allowed nested} (facts : RowControlFacts P Q)
    (keeps : RowKeeps P Q allowed nested) (catalog : Catalog) (frame : RowFrame) (cells : List Value)
    {state : KeyState} (good : P state) (step : Resolved.Step)
    (permitted : StepAllowed P allowed catalog frame cells step) :
    ResultHolds (fun pair : KeyState × Bool => P pair.1) Q (runStep catalog nested frame cells state step) := by
  cases step with
  | raise filter arms otherwise =>
    simp only [runStep]
    split
    · exact rowRaise facts good _
    · exact good
  | query query subqueries =>
    simp only [runStep]
    repeat' (first | split | dsimp only)
    all_goals first | exact facts.undescribed | exact facts.error _ _ good | exact facts.queried _ _ good
  | insert position rows clauses own subqueries =>
    simp only [runStep]
    split
    · rename_i table found
      exact ResultHolds.bind (keeps _ _ _ (permitted state table good found) good)
        fun _ reached => facts.afterStep _ _ _ reached
    · exact facts.undescribed
  | update position assignments filter subqueries =>
    simp only [runStep]
    split
    · rename_i table found
      exact ResultHolds.bind (keeps _ _ _ (permitted state table good found) good)
        fun _ reached => facts.afterStep _ _ _ reached
    · exact facts.undescribed
  | delete position filter subqueries =>
    simp only [runStep]
    split
    · rename_i table found
      exact ResultHolds.bind (keeps _ _ _ (permitted state table good found) good)
        fun _ reached => facts.afterStep _ _ _ reached
    · exact facts.undescribed

/-- A trigger program preserves the state/stop contract when entry is permitted and each
body step generates permitted work in its running frame. The proof checks entry and folds
the body; an ended row bypasses later steps without additional obligations. -/
theorem rowProgram {P Q allowed nested} (facts : RowControlFacts P Q)
    (keeps : RowKeeps P Q allowed nested) (catalog : Catalog) (frame : RowFrame) (cells : List Value)
    {state : KeyState} (good : P state) (program : Resolved.Program)
    (entry : allowed frame (.delete program.table [] false false false) state)
    (steps : ∀ step ∈ program.body,
      StepAllowed P allowed catalog { frame with running := program.trigger :: frame.running } cells step) :
    ResultHolds (fun pair : KeyState × Bool => P pair.1) Q
      (runProgram catalog nested frame cells state program) := by
  unfold runProgram
  split
  · exact good
  · refine ResultHolds.bind (rowEnter keeps frame program.table entry good) fun _ _ => ?_
    split
    · exact good
    · refine ResultHolds.foldlM_mem _ (fun pair step member good => ?_) (state, false) good
      obtain ⟨reached, ended⟩ := pair
      dsimp only
      split
      · exact good
      · exact rowStep facts keeps catalog _ cells good step (steps step member)

/-- The fired program sequence preserves the state/stop contract when every fired program
does so from each good input. The proof folds the actual list and bypasses the remaining
programs after the row ends. -/
theorem rowPrograms {P : KeyState → Prop} {Q : KeyStop → Prop}
    (catalog : Catalog) (nested : NestedRun) (frame : RowFrame)
    (table : Nat) (time : Syntax.TriggerTime) (event : Resolved.TriggerEvent) (cells : List Value)
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

#print axioms rowStep
#print axioms rowProgram
#print axioms rowPrograms

end ProofBoundaries
