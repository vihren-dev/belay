import Belay.Sqlite.Model.Queries.Select.RightJoinExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.MergedNameExamples
open Belay.Sqlite.Model Syntax Resolution.JoinExamples

/-- {lit}`t.b = r.e`, a written condition of two TEXT columns. -/
def onText : Expr := .compare .eq (qualified (name! "t") (name! "b")) (qualified (name! "r") (name! "e"))

end Belay.Sqlite.Model.Resolution.MergedNameExamples
