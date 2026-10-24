import Belay.Sqlite.ExecutionWP
import Std.Do

set_option doc.verso true

namespace Belay.Sqlite
open Std.Do

/-- The modeled-execution predicate transformer over the complete public context.
It checks all branches and rejects an unmodeled stop; SQL errors are governed by the
postcondition. Use the standard triple notation to compose these obligations. -/
def Sql.transformer {α : Type} (program : Sql α) : PredTrans (.arg ExecutionContext .pure) α where
  trans post state := ⟨program.check (fun value state => (post.1 value state).down) state⟩
  conjunctiveRaw first second := by
    apply SPred.bientails.of_eq
    ext state
    exact Sql.check_and program (fun value state => (first.1 value state).down)
      (fun value state => (second.1 value state).down) state

/-- Standard weakest-precondition rules for SQL, over its complete execution context.
Pure and bind follow their branch laws. Operational soundness is proved separately by
{name}`Sql.check_actual`; this instance does not assert the additional WPSound class. -/
instance sqlWPMonad : WPMonad Sql (.arg ExecutionContext .pure) where
  wp := Sql.transformer
  wp_pure value := by
    ext post state
    exact Sql.check_pure value (fun value state => (post.1 value state).down) state
  wp_bind program next := by
    ext post state
    exact Sql.check_bind program next (fun value state => (post.1 value state).down) state

/-- For every SQL triple, context satisfying its precondition and permitted branch,
that branch returns a value and satisfies the postcondition in its complete reached context.
The precondition may constrain arbitrary prefixes, clocks, counters or snapshots.
Proof sketch: unfold the standard triple and specialize its branch transformer. -/
theorem Sql.triple_branch {α : Type} {program : Sql α} {pre : ExecutionContext → Prop}
    {post : α → ExecutionContext → Prop}
    (triple : ⦃fun state => ⌜pre state⌝⦄ program ⦃⇓ value state => ⌜post value state⌝⦄)
    {state : ExecutionContext} (entry : pre state) {result : SqlRun α}
    (branch : program.Branch state.clock state.index state.connection result) :
    ∃ value, result.value = some value ∧ post value (state.finish result) := by
  have checked : program.check post state := triple state entry
  have holds := checked result branch
  cases returned : result.value with
  | none => simp [returned] at holds
  | some value => exact ⟨value, rfl, by simpa [returned] using holds⟩

/-- Every SQL triple holds for the actual interpreter at every context satisfying its
precondition, and that run returns a value. It uses the caller's whole context rather than
a fresh connection. Proof sketch: apply branch soundness to actual-run membership. -/
theorem Sql.triple_actual {α : Type} {program : Sql α} {pre : ExecutionContext → Prop}
    {post : α → ExecutionContext → Prop}
    (triple : ⦃fun state => ⌜pre state⌝⦄ program ⦃⇓ value state => ⌜post value state⌝⦄)
    {state : ExecutionContext} (entry : pre state) :
    ∃ value, (program.runFrom state.clock state.index state.connection).value = some value ∧
      post value (state.finish (program.runFrom state.clock state.index state.connection)) :=
  Sql.triple_branch triple entry (Sql.Branch.actual program _ _ _)

end Belay.Sqlite
