import Belay.Sqlite.Model.Queries.Select.DerivedResolutionExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.CommonTableResolutionExamples

open Syntax

/-- Mark a query as a WITH definition in its existing parent scope. -/
def definition (name : String) (body : Subquery) (columns : Option (List String) := none) : Subquery :=
  { body with commonTable := some {
      name := Identifier.ofString name
      columns := columns.map (List.map Identifier.ofString) } }

/-- Read a named CTE through the ordinary source syntax. -/
def fromName (name : String) (queries : List Subquery) : Syntax.Statement :=
  .select [.star] (some { table := Identifier.ofString name, alias := none }) [] none [] [] none none queries

end Belay.Sqlite.Model.Resolution.CommonTableResolutionExamples
