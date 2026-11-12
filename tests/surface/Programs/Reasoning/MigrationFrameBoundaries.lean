import ExecutionViewComposition
import MigrationPatterns

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace MigrationCompositionExamples
open Belay.Sqlite Belay.Sqlite.Model ExecutionViewComparisonExamples

/-- A deterministic continued step with a constant returned value has one branch.
Proof sketch: invert the step, fix its selected output, and invert the pure tail. -/
private theorem constant_branch {α : Type} {statement values clock index connection output next}
    (step : runScriptStep runContext clock index connection statement values = .continued output next [])
    (only : ∀ selected, OutputChoice output selected → selected = output) (value : α) (result : SqlRun α) :
    (Sql.exec statement values (fun _ => .pure value)).Branch clock index connection result ↔
      result = { outputs := [output], connection := next, value := some value } := by
  constructor
  · intro branch
    obtain ⟨selected, tail, choice, later, rfl⟩ := (Sql.branch_continued_iff step result).mp branch
    have selectedEq := only selected choice
    subst selected
    have tailEq := (Sql.branch_pure_iff value _ _ _ tail).mp later
    subst tail
    rfl
  · rintro rfl
    exact Sql.Branch.continued_own (rest := fun _ => .pure value) step (.actual output) (.pure value _ _ _)

/-- This migration stores its statement-indexed clock value while returning no SQL output. -/
def clockWrite : Sql Unit :=
  let (statement, values) := (sql r"UPDATE t SET x=CURRENT_TIMESTAMP WHERE id=1").statements[0]
  .exec statement values fun _ => .pure ()

/-- The clock migration at the original index has one completed write branch.
Proof sketch: reduce its step and invert the deterministic done output. -/
private theorem clock_unique (result : SqlRun Unit) :
    clockWrite.Branch initial.clock initial.index initial.connection result ↔
      result = clockWrite.runFrom initial.clock initial.index initial.connection := by
  apply constant_branch (output := .done 1)
    (next := (clockWrite.runFrom initial.clock initial.index initial.connection).connection) (by rfl)
  intro selected choice
  exact choice.elim id False.elim

/-- The constant read after the clock write leaves that exact reached connection
unchanged. Proof sketch: reduce its deterministic step and invert its pure tail. -/
private theorem read_after_clock_unique (result : SqlRun Nat) :
    one.Branch initial.clock 1
        (clockWrite.runFrom initial.clock initial.index initial.connection).connection result ↔
      result = { outputs := [.rows [[1]]], connection :=
        (clockWrite.runFrom initial.clock initial.index initial.connection).connection, value := some 7 } := by
  apply constant_branch (output := .rows [[1]]) (by rfl)
  intro selected choice
  simpa [OutputChoice] using choice

/-- Every branch of the migrated constant read has the same value and visible query
output. Its changed connection is deliberately absent from this weak fact.
Proof sketch: split the migration and read, using each unique branch. -/
private theorem clock_after_unique (result : SqlRun Nat) :
    (Migration.after clockWrite one).Branch initial.clock initial.index initial.connection result ↔
      result = (Migration.after clockWrite one).runFrom initial.clock initial.index initial.connection := by
  rw [Migration.after, Sql.branch_bind_iff]
  simp only [clock_unique, exists_eq_left]
  change (∃ last, one.Branch initial.clock 1
      (clockWrite.runFrom initial.clock initial.index initial.connection).connection last ∧
      result = { last with outputs := [.done 1] ++ last.outputs }) ↔ _
  simp only [read_after_clock_unique, exists_eq_left]
  rfl

/-- The clock-writing migration weakly preserves the constant query at this context.
This is a nonvacuous preservation claim, checked over the actual and every branch. -/
theorem clock_weak_preservation : Migration.Domain clockWrite (fun _ => True) initial ∧
    Migration.PreservesAt clockWrite (fun _ => True) one initial := by
  refine ⟨⟨True.intro, by decide +kernel⟩, ?_⟩
  intro _
  apply observationProfile_eq_iff.mpr
  constructor
  · rfl
  · intro observed
    change (∃ result, one.Branch initial.clock initial.index initial.connection result ∧ _) ↔
      (∃ result, (Migration.after clockWrite one).Branch initial.clock initial.index initial.connection result ∧ _)
    simp only [one_unique, clock_after_unique, exists_eq_left]
    rfl

/-- Moving a constant read before the migration shifts the stored clock value by one
statement. Weak preservation therefore does not imply full commutation, even though
both orders return 7 and expose the same constant row. Proof sketch: project the final
stored rows from actual full equality and reduce the unequal dates. -/
theorem clock_blocks_full_commutation : ¬ Migration.CommutesAt clockWrite (fun _ => True) one initial := by
  intro same
  have rows := congrArg (fun observed => observed.2.connection.state.database.rowsAt 0)
    (observationProfile_actual (same clock_weak_preservation.1))
  have different :
      ((Migration.before one clockWrite).runFrom initial.clock initial.index initial.connection).connection.state.database.rowsAt 0 ≠
      ((Migration.after clockWrite one).runFrom initial.clock initial.index initial.connection).connection.state.database.rowsAt 0 := by
    decide +kernel
  exact different rows

/-- A hidden BEGIN changes the saved transaction snapshot despite equal raw step count
and returned value. Complete connection equality must retain that snapshot. -/
theorem snapshot_blocks_full :
    let begin : Sql Nat := (send (sql r"BEGIN")).bind fun _ => .pure 7
    ¬ (Sql.View.quiet one).EquivAt (Sql.View.quiet begin) initial := by
  dsimp only
  intro same
  have snapshots := congrArg (fun observed => observed.2.connection.state.snapshot.isSome) (observationProfile_actual same)
  have impossible : false = true := snapshots
  cases impossible

#print axioms clock_weak_preservation
#print axioms clock_blocks_full_commutation
#print axioms snapshot_blocks_full
#print axioms ExecutionViewComparisonExamples.not_full_extra_step
#print axioms MigrationPatternExamples.counters_remain_visible
end MigrationCompositionExamples
