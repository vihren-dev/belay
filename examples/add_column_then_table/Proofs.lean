import Generated
import SqliteVerifier.Demonstration

/-! The public theorem binds these exact statements, catalogs, and observations. -/
namespace Proofs

/-- No data fixture or additional starting condition is assumed. -/
theorem migrationCorrect : Generated.expected :=
  SqliteVerifier.Demonstration.migrationCorrect Generated.profile (by decide)

end Proofs
