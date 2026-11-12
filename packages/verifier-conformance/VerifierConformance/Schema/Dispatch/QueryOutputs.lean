import Belay.Sqlite.Model.Schema.Dispatch.SqlAdvance
import VerifierConformance.Queries.Preparation.QueryOutputs

set_option doc.verso true

namespace Belay.Sqlite.Model.Conformance.QueryOutputs

#guard match advance 0 (.query Resolved.QueryExamples.grouped []) [] { database } with
  | .next next => next.database.table 0 == database.table 0 && next.snapshot.isNone
  | .halt _ => false

end Belay.Sqlite.Model.Conformance.QueryOutputs
