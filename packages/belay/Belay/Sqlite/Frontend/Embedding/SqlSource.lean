import Lean.Meta.Basic
import Lean.Syntax
import Belay.Sqlite.Shared.Execution.Script

set_option doc.verso true

namespace Belay.Sqlite

open Lean

/-- The metadata key for an SQL script's original literal text. -/
def scriptSourceKey : Name := `Belay.Sqlite.source.script

/-- The metadata key for a database construction's original literal text. -/
def databaseSourceKey : Name := `Belay.Sqlite.source.database

/-- The metadata key for the original literal syntax, retaining its source range. -/
def sourceRangeKey : Name := `Belay.Sqlite.source.range

/-- The metadata key for the file containing the original SQL literal. -/
def sourceFileKey : Name := `Belay.Sqlite.source.file

/-- Attach text and source range to an expression as definitionally irrelevant metadata.
Use {name}`scriptSourceKey` for a script and {name}`databaseSourceKey` for a database.
The text is a hint, not evidence that the expression has any particular value. -/
def withSource (key : Name) (literal : Syntax) (text fileName : String) (expression : Expr) : Expr :=
  mkMData (((KVMap.empty.insert key (.ofString text)).insert sourceRangeKey (.ofSyntax literal)).insert
    sourceFileKey (.ofString fileName)) expression

end Belay.Sqlite
