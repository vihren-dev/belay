import Belay.Sqlite.Model.Shared.Execution.SqlExecution
import Belay.Sqlite.Model.Queries.Fixtures.Examples

set_option doc.verso true

namespace Belay.Sqlite.Model.ValidityExamples

open Belay.Sqlite.Model Syntax

/-- A text literal. -/
def text (value : String) : Expr := .string value.toUTF8.toList

/-- A name as written, without quotes. -/
def name (value : String) : Expr := .identifier (Identifier.ofString value) .none

end Belay.Sqlite.Model.ValidityExamples
