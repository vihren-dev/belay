import ExecutionViewChoices
import Belay.Sqlite.MigrationPatternFrames

set_option doc.verso true
set_option maxRecDepth 8192

namespace MigrationCompositionExamples
open Belay.Sqlite Belay.Sqlite.Model ExecutionViewComparisonExamples

/-- The one-step constant query has exactly its actual branch at every clock and index
on this fixture's connection. Proof sketch: invert its deterministic output and pure tail. -/
theorem one_unique (clock : Option Clock) (index : Nat) (result : SqlRun Nat) :
    one.Branch clock index initial.connection result ↔
      result = { outputs := [.rows [[1]]], connection := initial.connection, value := some 7 } := by
  have step : let (statement, values) := (sql r"SELECT 1").statements[0]
      runScriptStep runContext clock index initial.connection statement values =
        .continued (.rows [[1]]) initial.connection [] := rfl
  constructor
  · intro branch
    obtain ⟨selected, later, choice, tail, rfl⟩ := (Sql.branch_continued_iff step result).mp branch
    have selectedEq : selected = .rows [[1]] := by simpa [OutputChoice] using choice
    subst selected
    have laterEq := (Sql.branch_pure_iff 7 _ _ _ later).mp tail
    subst later
    rfl
  · rintro rfl
    exact Sql.Branch.continued_own (rest := fun _ => .pure 7) step (.actual _) (.pure 7 _ _ _)

/-- Two copies of the constant query also have one complete branch, with two raw steps.
Proof sketch: split bind and use the one-step classification for both segments. -/
theorem two_unique (clock : Option Clock) (index : Nat) (result : SqlRun Nat) :
    (Migration.after one one).Branch clock index initial.connection result ↔
      result = { outputs := [.rows [[1]], .rows [[1]]], connection := initial.connection, value := some 7 } := by
  rw [Migration.after, Sql.branch_bind_iff]
  simp only [one_unique, exists_eq_left]
  rfl

/-- The contextual example admits every prior trace and index, while fixing the valid
connection. This is an intermediate-context domain rather than a fresh reset. -/
def connected (state : ExecutionContext) : Prop := state.connection = initial.connection

/-- The nonempty migration preserves the query on the declared intermediate contexts.
Proof sketch: classify both raw branch sets; the migration's extra success output is hidden. -/
theorem one_preserves : Migration.PreservesOn one connected one := by
  intro state entry
  have connection : state.connection = initial.connection := entry.1
  constructor
  · cases state with
    | mk clock index current outputs => cases connection; rfl
  · intro observed
    change (∃ result, one.Branch state.clock state.index state.connection result ∧ _) ↔
      (∃ result, (Migration.after one one).Branch state.clock state.index state.connection result ∧ _)
    simp only [connection, one_unique, two_unique, exists_eq_left]
    rfl

/-- Every returning migration branch retains the declared connection domain.
Proof sketch: its unique branch leaves the full connection unchanged. -/
theorem one_reaches : one.ReturnsIn connected (fun _ => connected) := by
  intro state entry result branch value returned
  rw [entry] at branch
  have equal := (one_unique state.clock state.index result).mp branch
  subst result
  rfl

/-- Two nonempty migrations preserve the query by the public composition theorem;
all intermediate clocks, indices and traces remain in the supplied contextual domain. -/
theorem composed_preservation : Migration.PreservesOn (Migration.after one one) connected one :=
  Migration.PreservesOn.compose one_preserves one_preserves one_reaches

/-- The positive full bridge discharges its later-success, complete-connection and raw
step-count premises from the two deterministic executions. Both segments execute SQL.
Proof sketch: classify application and both two-step orders, then apply the frame bridge. -/
theorem positive_commutation : Migration.CommutesAt one connected one initial := by
  apply (one_preserves initial).commutes_of_frames
  · intro _ result branch value returned
    have equal := (one_unique _ _ result).mp branch
    subst result
    decide +kernel
  · intro _ left right before after _
    have leftEq := (two_unique _ _ left).mp (show (Migration.after one one).Branch _ _ _ left from before)
    have rightEq := (two_unique _ _ right).mp after
    cases leftEq; cases rightEq; rfl
  · intro _ left right before after _
    have leftEq := (two_unique _ _ left).mp (show (Migration.after one one).Branch _ _ _ left from before)
    have rightEq := (two_unique _ _ right).mp after
    cases leftEq; cases rightEq; rfl

#print axioms one_unique
#print axioms two_unique
#print axioms one_preserves
#print axioms one_reaches
#print axioms composed_preservation
#print axioms positive_commutation
#print axioms Sql.succeedsFrom_iff_branches
#print axioms Sql.succeedsFrom_bind_iff
#print axioms Sql.View.project_quiet_of_allOk
#print axioms Migration.quiet_return_observation
#print axioms Migration.before_observation
#print axioms Migration.after_compose
#print axioms Migration.TranslatesOn.compose
#print axioms Migration.PreservesOn.compose
#print axioms Migration.TranslatesAt.commutes_of_frames
#print axioms Migration.TranslatesOn.commutes_of_frames
end MigrationCompositionExamples
