import Belay.Sqlite.Model.Queries.Select.QueryResolutionExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.DeleteExamples
open Belay.Sqlite.Model Syntax

/-- The filter {lit}`Abc = 1` as written. -/
def abcIsOne : Syntax.Expr := .compare .eq (.identifier (name! "Abc") .none) (.numeric "1")

/-- A table with a row where {lit}`Abc` is 1 and a row where it is NULL. -/
def table : Table :=
  { shape := { columns := [{ name := (name! "Abc"), declaredType := some "INTEGER" },
      { name := (name! "b"), declaredType := some "TEXT" }] },
    rows := [{ rowid := 1, values := [.integer 1, .text [97]] }, { rowid := 2, values := [.null, .text [98]] }] }

end Belay.Sqlite.Model.Resolution.DeleteExamples
