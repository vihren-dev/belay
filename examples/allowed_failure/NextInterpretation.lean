import Interpretation
import SqlInputs
import SqliteVerifier.Demonstration

/-! The committed prefix is represented after the explicitly allowed modeled error. -/
namespace NextInterpretation

/-- Read every protected invoice row from the resulting prefix storage. -/
def next : SqliteVerifier.Interpretation Requirements.LogicalState :=
  SqliteVerifier.projectedInterpretation Generated.profile Generated.nextCatalog "invoices" ["amount"]

/-- Every declared failure representation uses the catalog of the committed prefix,
without the unreached table, and the same invoice reader. -/
def failures : SqliteVerifier.FailureRepresentation Requirements.LogicalState where
  catalog := fun _ _ => SqliteVerifier.Demonstration.nextCatalog
  interpretation := fun _ _ => SqliteVerifier.Demonstration.next Generated.profile

end NextInterpretation
