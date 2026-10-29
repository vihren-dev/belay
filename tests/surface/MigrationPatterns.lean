import ExecutionViewComparisons
import Belay.Sqlite.MigrationPatternLaws

set_option doc.verso true
set_option maxRecDepth 8192

namespace MigrationPatternExamples
open Belay.Sqlite Belay.Sqlite.Model ExecutionViewComparisonExamples

/-- The migration succeeds initially but collides after the application inserts its key. -/
def migration : Sql (List Output) := send (sql r"INSERT INTO t VALUES (3, 30)")

/-- The application returns a structured value after inserting the migration's future key. -/
def application : Sql (Nat × String) :=
  (send (sql r"INSERT INTO t VALUES (3, 300)")).bind fun _ => .pure (7, "application")

/-- Earlier trace errors do not exclude success of the original migration.
The domain checks the supplied current connection, not accumulated prefix success. -/
theorem original_domain : Migration.Domain migration (fun _ => True) initial := by
  constructor
  · trivial
  · decide +kernel

/-- Both commutation orders retain the application's value despite the SQL conflict
in different segments. Their projected failures are different observations. -/
theorem returned_application :
    let left := (Migration.before application migration).runFrom initial.clock initial.index initial.connection
    let right := (Migration.after migration application).runFrom initial.clock initial.index initial.connection
    left.value = some (7, "application") ∧ right.value = some (7, "application") ∧
    (Migration.beforeView application migration).project left.outputs = [.done 1, .error 19] ∧
    (Migration.afterView migration application).project right.outputs = [.error 19] := by decide +kernel

/-- The moved migration fails, but the original success domain remains inhabited;
the claimed full commutation is false. Proof sketch: instantiate the original domain
and contradict the computed unequal projected actual observations. -/
theorem moved_failure_not_hidden : ¬ Migration.CommutesAt migration (fun _ => True) application initial := by
  intro commutes
  have same := commutes original_domain
  have unequal :
      (Migration.beforeView application migration).fullObservation initial
        ((Migration.before application migration).runFrom initial.clock initial.index initial.connection) ≠
      (Migration.afterView migration application).fullObservation initial
        ((Migration.after migration application).runFrom initial.clock initial.index initial.connection) := by
    intro equal
    have outputs := congrArg (fun observed => observed.2.outputs.length) equal
    have impossible : (3 : Nat) = 2 := outputs
    cases impossible
  exact unequal (observationProfile_actual same)

/-- A migration that already fails at the original context lies outside the convenient
domain. This is a vacuous comparison, not a proof that either program succeeds. -/
theorem failed_original_vacuity :
    let failed := send (sql r"INSERT INTO t VALUES (1, 99)")
    ¬ Migration.Domain failed (fun _ => True) initial ∧
      Migration.CommutesAt failed (fun _ => True) application initial := by
  dsimp only
  have failed : ¬ (send (sql r"INSERT INTO t VALUES (1, 99)")).SucceedsFrom
      initial.clock initial.index initial.connection := by decide +kernel
  exact ⟨fun entry => failed entry.2, Migration.commutesAsAt_of_failure _ _ _ _ _ failed⟩

/-- A pure migration preserves the read-only query for every valid bundled database
and complete environment, with no concrete schema restriction hidden in this claim. -/
theorem universal_identity : Migration.QueryPreserves (.pure () : Sql Unit)
    (sql r"SELECT 1") (fun _ => True) :=
  Migration.queryPreserves_pure () _ _ rfl

/-- Full comparison retains counters even when both quiet programs take one step
and return the same value. Proof sketch: actual {lit}`total_changes` values are 0 and 1. -/
theorem counters_remain_visible :
    let write := (send (sql r"UPDATE t SET x=9 WHERE id=1")).bind fun _ => (.pure 7 : Sql Nat)
    ¬ (Sql.View.quiet one).EquivAt (Sql.View.quiet write) initial := by
  dsimp only
  intro same
  have count := congrArg (fun observed => observed.2.connection.state.counters.totalChanges) (observationProfile_actual same)
  have impossible : (some 0 : Option Nat) = some 1 := count
  cases impossible

#print axioms original_domain
#print axioms returned_application
#print axioms moved_failure_not_hidden
#print axioms failed_original_vacuity
#print axioms universal_identity
#print axioms counters_remain_visible
#print axioms Migration.preserves_pure
#print axioms Migration.queryPreserves_pure
#print axioms Migration.TranslatesOn.restrict
#print axioms Migration.CommutesAsOn.restrict
#print axioms Migration.translatesAt_of_failure
#print axioms Migration.commutesAsAt_of_failure
end MigrationPatternExamples
