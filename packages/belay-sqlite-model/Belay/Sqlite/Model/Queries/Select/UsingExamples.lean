import Belay.Sqlite.Model.Queries.Select.JoinExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.UsingExamples
open Belay.Sqlite.Model Syntax Resolution.JoinExamples

/-- A join with {lit}`USING` and the names. -/
def usingJoin (operator : List String) (name : Identifier) (names : List Identifier) : Join :=
  { joined operator (table name) with usingColumns := some names }

/-- An unqualified column as a result column. -/
def bare (name : Identifier) : ResultColumn := .expression (.identifier name .none) none name.text

end Belay.Sqlite.Model.Resolution.UsingExamples
