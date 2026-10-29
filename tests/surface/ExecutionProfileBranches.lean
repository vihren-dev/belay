import InsertSelectExecutions
import Belay.Sqlite.MigrationPatternSuccess

set_option doc.verso true

/-! Profiles retain the alternate databases and failures of the existing INSERT-SELECT fixtures. -/
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace InsertSelectExecutionExamples
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- Every copy branch succeeds and the actual first row is 20, but the full profile
rejects that row guarantee: a permitted database differs. Proof sketch: reuse the
existing all-branch success and first-row counterexample through the profile predicate. -/
theorem profile_keeps_alternate_database :
    copy.SucceedsFrom none 0 start.connection ∧
    (names (start.finish (copy.runFrom start.clock start.index start.connection))).head? = some (.integer 20) ∧
    ¬ ∀ result, (observationProfile (copy.runFrom start.clock start.index start.connection)
      (copy.Branch start.clock start.index start.connection) id).2 result →
      match result.value with
      | none => False
      | some _ => (start.finish result).outputs.allOk = true ∧
          (names (start.finish result)).head? = some (.integer 20) := by
  refine ⟨copy_succeeds, by decide +kernel, ?_⟩
  intro all
  apply first_row_claim_fails
  intro result branch
  have post := all result ⟨result, branch, rfl⟩
  cases returned : result.value <;> simpa only [returned] using post

/-- The actual limited insertion succeeds while its profile rejects universal success.
Proof sketch: the profile predicate is the branch predicate, so the existing
universal-success counterexample applies; compute actual success independently. -/
theorem profile_keeps_alternate_failure :
    let profile := observationProfile (limited.runFrom none 0 emptyStart.connection)
      (limited.Branch none 0 emptyStart.connection) id
    (profile.1.value.isSome = true ∧ List.allOk profile.1.outputs = true) ∧
      ¬ ∀ result, profile.2 result →
        result.value.isSome = true ∧ List.allOk result.outputs = true := by
  refine ⟨by decide +kernel, ?_⟩
  simpa only [observationProfile, id_eq, exists_eq_right,
    ← Sql.succeedsFrom_iff_branches] using some_execution_fails

#print axioms profile_keeps_alternate_database
#print axioms profile_keeps_alternate_failure
#print axioms observationProfile_eq_iff
#print axioms observationProfile_id_eq_iff
#print axioms observationProfile_actual
#print axioms observationProfile_transport
#print axioms observationProfile_of_singletons
end InsertSelectExecutionExamples
