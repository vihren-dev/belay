import Interpretation
import SqlInputs
import SqliteVerifier.Demonstration

/-! The committed prefix is represented after the explicitly allowed modeled error. -/
namespace NextInterpretation

/-- Read every protected invoice row from the resulting prefix storage. -/
def next : SqliteVerifier.Interpretation Requirements.LogicalState :=
  SqliteVerifier.projectedInterpretation Generated.profile Generated.nextCatalog "invoices" ["amount"]

/-- Every declared failure representation reads the committed prefix, whose catalog has
no unreached table, with the same invoice reader. -/
def failures : SqliteVerifier.FailureRepresentation Requirements.LogicalState where
  interpretation := fun _ _ => SqliteVerifier.Demonstration.next Generated.profile

end NextInterpretation
