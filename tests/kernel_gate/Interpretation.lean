import Requirements
import SchemaInputs

/-! Approved empty-catalog interpretation for the kernel-gate fixture. -/
namespace Interpretation
/-- No additional starting condition is needed for an empty catalog. -/
def admitted (_ : Belay.Sqlite.Model.Database) : Prop := True
/-- Preserve exact empty-catalog conformance while observing one unit value. -/
def current : SqliteVerifier.Interpretation Requirements.LogicalState :=
  ⟨Belay.Sqlite.Model.Conforms Generated.profile Generated.startCatalog, fun _ => some ()⟩
end Interpretation
