import Interpretation
import SqlInputs

/-! This candidate uses the same logical projection after a different statement order. -/
namespace NextInterpretation

/-- Read all protected rows and amounts from the resulting catalog. -/
def next : SqliteVerifier.Interpretation Requirements.LogicalState :=
  SqliteVerifier.projectedInterpretation Generated.profile Generated.nextCatalog "invoices" ["amount"]

/-- Explicit success applicability rules out modeled failures. -/
def failures : SqliteVerifier.FailureRepresentation Requirements.LogicalState :=
  SqliteVerifier.unreachableFailures

end NextInterpretation
