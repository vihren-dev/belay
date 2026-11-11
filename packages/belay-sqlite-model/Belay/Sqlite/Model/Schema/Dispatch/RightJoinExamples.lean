import Belay.Sqlite.Model.Schema.Dispatch.UsingExamples
import Belay.Sqlite.Model.Queries.Select.RightJoinExamples

set_option doc.verso true

/-! Examples of {lit}`RIGHT` and {lit}`FULL` joins (ADR 0012, amendment 3; slice 4c),
checked by {lit}`#guard`: the resolved kinds and the rows of the joins. -/

namespace Belay.Sqlite.Model.Resolution.RightJoinExamples
open Belay.Sqlite.Model Syntax Resolution.JoinExamples Resolution.UsingExamples

-- The operators resolve to their kinds.
#guard (queryOver [.star] (table (name! "t")) [joined ["RIGHT"] (table (name! "u")) (some onA)]).map (fun query => (query.sources.drop 1).map (·.kind)) ==
  some [.right]
#guard (queryOver [.star] (table (name! "t")) [joined ["full", "Outer"] (table (name! "u")) (some onA)]).map (fun query => (query.sources.drop 1).map (·.kind)) ==
  some [.full]

-- The source of a query folds the joins with the width of the tables so far.
#guard (fullQuery.source (.plain 0) (.ofTables [((name! "l"), JoinExamples.left), ((name! "r"), rightTwo)])).map (·.rows) ==
  some [[.integer 1, .integer 1], [.integer 2, .null], [.null, .integer 3]]

end Belay.Sqlite.Model.Resolution.RightJoinExamples
