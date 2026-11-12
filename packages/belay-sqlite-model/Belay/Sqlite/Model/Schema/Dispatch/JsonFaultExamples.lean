import Belay.Sqlite.Model.Schema.Dispatch.StatementStep
import Belay.Sqlite.Model.Values.Json.JsonFaultExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved.JsonFaultExamples

#guard match step 0 {} [] (.query fromless []) empty with
  | .error (reason, _) => reason == .functionError
  | .ok _ => false

-- The model gives a write no JSON error: a DELETE whose WHERE may fail is not ready.
#guard (empty.table 0).all fun table => !deleteJsonReady (.plain 0) table (some malformed) [] && deleteJsonReady (.plain 0) table (some selected) []

end Belay.Sqlite.Model.Resolved.JsonFaultExamples
