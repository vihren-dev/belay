import Generated
import SqliteVerifier.ReverseDemonstration

/-! Reuse the exact approved requirements while checking the reversed script. -/
namespace Proofs

/-- Statement order is justified by the public run-equivalence proof. -/
theorem migrationCorrect : Generated.expected :=
  SqliteVerifier.Demonstration.reverseMigrationCorrect Generated.profile (by decide)

end Proofs
