import Belay.Sqlite.Model.Queries.Evaluation.QueryExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Conformance.QueryOutputs

open Resolved.QueryExamples in
/-- A database with the example table of {lit}`Belay.Sqlite.Model.Resolved.QueryExamples`
at catalog position 0. -/
def database : Database := .ofTables [((name! "t"), table)]

end Belay.Sqlite.Model.Conformance.QueryOutputs
