import Requirements
import SchemaInputs

/-! Approved empty-catalog interpretation for the kernel-gate fixture. -/
namespace Interpretation
/-- No additional starting condition is needed for an empty catalog. -/
def admitted (_ : Belay.Sqlite.Database) : Prop := True
/-- Preserve exact empty-catalog conformance while observing one unit value. -/
def current : SqliteVerifier.Interpretation Requirements.LogicalState :=
  ⟨Belay.Sqlite.Conforms Generated.profile Generated.startCatalog, fun _ => some ()⟩
end Interpretation
