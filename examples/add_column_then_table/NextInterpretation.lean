import Interpretation
import SqlInputs

/-! Candidate meaning is read from the resulting storage under its exact catalog. -/
namespace NextInterpretation

/-- All old invoice rows and amounts remain protected. -/
def next : SqliteVerifier.Interpretation Requirements.LogicalState :=
  SqliteVerifier.projectedInterpretation Generated.profile Generated.nextCatalog "invoices" ["amount"]

/-- The proof establishes successful applicability, so modeled failure is unreachable. -/
def failures : SqliteVerifier.FailureRepresentation Requirements.LogicalState :=
  SqliteVerifier.unreachableFailures

end NextInterpretation
