import Belay.Sqlite.Model.Shared.Execution.ScriptRun
import Belay.Sqlite.Model.Schema.Dispatch.Examples

set_option doc.verso true

namespace Belay.Sqlite.Model.ScriptRunExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- {lit}`CREATE TABLE t(id INTEGER PRIMARY KEY, name TEXT)`. -/
def createT : Syntax.Statement :=
  .createTable (name! "t")
    [{ name := name! "id", declaredType := some "INTEGER", constraints := [.primaryKey false] },
      column (name! "name")] []

/-- {lit}`INSERT INTO t VALUES (id, name)`, with the algorithm of {lit}`INSERT OR algorithm`. -/
def insertT (id : String) (text : String) (algorithm : Option ConflictAlgorithm := none) : Syntax.Statement :=
  .insert (name! "t") none [[.numeric id, .string text.toUTF8.toList]] [] algorithm

/-- {lit}`INSERT INTO c(a) VALUES ('x')`, which gives b its default. -/
def insertClocked : Syntax.Statement := .insert (name! "c") (some [name! "a"]) [[.string "x".toUTF8.toList]] []

end Belay.Sqlite.Model.ScriptRunExamples
