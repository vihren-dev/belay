import SchemaInputs
import Requirements

set_option doc.verso true

/-! Approved key identity comes from actual stored amounts. The sealed resolution
of the schema supplies the representation's conformance requirement. -/

namespace Interpretation

/-- For the given database, require a defined logical-key read. Missing table,
column or cell, NULL keys and duplicate keys are refused; the empty invoice
table is admitted. Catalog conformance remains part of the generated target. -/
def admitted : Belay.Sqlite.Model.Database → Prop :=
  SqliteVerifier.ApplicationKeyDemonstration.admitted

/-- Observe actual invoice keys and protected amounts under the sealed starting
catalog. Physical rowids are omitted, and the contract compares full records
with permutation. General interpretation constructors allow another policy. -/
def current : SqliteVerifier.Interpretation Requirements.LogicalState :=
  SqliteVerifier.applicationKeyInterpretation Generated.profile Generated.startCatalog
    SqliteVerifier.ApplicationKeyDemonstration.invoiceTableName
    SqliteVerifier.ApplicationKeyDemonstration.invoiceKeyNames
    SqliteVerifier.ApplicationKeyDemonstration.invoiceProtectedFields

end Interpretation
