import MigrationComposition
import Belay.Sqlite.MigrationApplicationLaws

set_option doc.verso true
set_option maxRecDepth 8192

namespace MigrationCompositionExamples
open Belay.Sqlite Belay.Sqlite.Model ExecutionViewComparisonExamples

/-- The same nonempty constant query commutes at every context with this connection,
including arbitrary prior traces and raw indices. Proof sketch: classify both two-step
branch sets and reduce their identical actual runs and projected observations. -/
theorem one_commutes : Migration.CommutesOn one connected one := by
  intro state entry
  have connection : state.connection = initial.connection := entry.1
  apply observationProfile_eq_iff.mpr
  constructor
  · cases state with
    | mk clock index current outputs => cases connection; rfl
  · intro observed
    change (∃ result, (Migration.after one one).Branch state.clock state.index state.connection result ∧ _) ↔
      (∃ result, (Migration.after one one).Branch state.clock state.index state.connection result ∧ _)
    simp only [connection, two_unique, exists_eq_left]
    rfl

/-- Composing the nonempty application with a value-dependent return preserves full
commutation. The reached predicate includes its raw output, not a projected trace.
Proof sketch: use the public bind rule, classify the first query branch and prove
migration success on that exact connection through all its branches. -/
theorem nonempty_application_bind :
    Migration.CommutesOn one connected (one.bind fun value => .pure (value + 1)) := by
  apply Migration.CommutesOn.bind (post := fun _ state => connected state ∧ state.outputs.length > 0)
    one_commutes (fun value => Migration.commutes_pure_application one (value + 1) _) ?_
  intro state entry result branch value returned
  have connection : state.connection = initial.connection := entry.1
  rw [connection] at branch
  have equal := (one_unique state.clock state.index result).mp branch
  subst result
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp [ExecutionContext.finish]
  · apply (Sql.succeedsFrom_iff_branches one _ _ _).mpr
    intro later permitted
    have equal := (one_unique _ _ later).mp permitted
    subst later
    exact ⟨rfl, rfl⟩

/-- The composed positive case has an inhabited original-success domain, and both
orders return the continuation's value 8 after executing their SQL segments.
Proof sketch: evaluate the original migration and the two ordinary executions. -/
theorem nonempty_bind_witness :
    Migration.Domain one connected initial ∧
      ((Migration.before (one.bind fun value => .pure (value + 1)) one).runFrom
        initial.clock initial.index initial.connection).value = some 8 ∧
      ((Migration.after one (one.bind fun value => .pure (value + 1))).runFrom
        initial.clock initial.index initial.connection).value = some 8 :=
  ⟨⟨rfl, by decide +kernel⟩, rfl, rfl⟩

/-- The application composition law yields the actual full comparison at that
inhabited context. Proof sketch: apply the law to the separately checked domain. -/
theorem nonempty_bind_comparison :
    (Migration.beforeView (one.bind fun value => .pure (value + 1)) one).EquivAt
      (Migration.afterView one (one.bind fun value => .pure (value + 1))) initial :=
  nonempty_application_bind initial nonempty_bind_witness.1

/-- The application bind law retains result-dependent tails on every raw and concrete
LIMIT branch. Its sufficient reached domain observes the full raw prefix length.
Proof sketch: pure migration commutation applies to every tail; inversion of the
query branch supplies the two-entry reached trace, including the existing error. -/
theorem choice_application_bind :
    Migration.CommutesOn (.pure ()) (fun state => state = initial)
      ((choices false).bind fun value => .pure (value + 1)) := by
  apply Migration.CommutesOn.bind (post := fun _ state => state.outputs.length = 2)
    (Migration.commutes_pure_migration () (choices false) _)
    (fun value => Migration.commutes_pure_application (.pure ()) (value + 1) _) ?_
  intro state entry result branch value returned
  have stateEq := entry.1
  subst state
  obtain ⟨selected, later, choice, tail, rfl⟩ := (Sql.branch_continued_iff choices_step result).mp branch
  have laterEq := (Sql.branch_pure_iff _ _ _ _ later).mp tail
  subst later
  exact ⟨rfl, True.intro⟩

#print axioms one_commutes
#print axioms nonempty_application_bind
#print axioms nonempty_bind_witness
#print axioms nonempty_bind_comparison
#print axioms choice_application_bind
#print axioms Sql.View.project_bind_congr
#print axioms Migration.before_bind
#print axioms Migration.after_bind
#print axioms Migration.before_then
#print axioms Migration.commutes_pure_migration
#print axioms Migration.commutes_pure_application
#print axioms Migration.CommutesAsOn.bind
#print axioms Migration.CommutesOn.bind
#print axioms Migration.CommutesAsOn.bind_unrestricted
end MigrationCompositionExamples
