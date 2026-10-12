import SqlInputs
import NextInterpretation

/-! This candidate-side alias is useful to authors but is not trusted by the gate. -/
namespace Generated
/-- The author-facing expected proposition. -/
def expected : Prop := SqliteVerifier.VerificationConditions
  startCatalog nextCatalog resolved Interpretation.admitted Requirements.contract
  Interpretation.current NextInterpretation.next NextInterpretation.failures profile
end Generated
