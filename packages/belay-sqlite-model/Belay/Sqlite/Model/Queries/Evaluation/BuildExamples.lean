import Belay.Sqlite.Model.Queries.Evaluation.ExprEval
import Belay.Sqlite.Model.Values.Json.BuildExamples

set_option doc.verso true

/-! Checked examples of the JSON functions that build or edit text (ADR 0015, slice 3), and of
the JSON subtype of their arguments. Each result was checked on native SQLite 3.51.0, one
statement per line. -/

namespace Belay.Sqlite.Model.Json.BuildExamples

open Belay.Sqlite.Model Belay.Sqlite.Model.Json Belay.Sqlite.Model.Json.ExampleSupport

example : (subtypeCall.evaluate (.plain 0) []).1 = sqlText "[[1],[2],\"[3]\"]" := by decide +kernel

end Belay.Sqlite.Model.Json.BuildExamples
