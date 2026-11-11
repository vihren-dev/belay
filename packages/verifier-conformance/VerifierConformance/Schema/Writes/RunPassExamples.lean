import Belay.Sqlite.Model.Queries.Preparation.ScriptRunExamples
import Belay.Sqlite.Model.Schema.Writes.ScriptRunExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Conformance.RunPassExamples

open Belay.Sqlite.Model Syntax ScriptRunExamples

/-- The statements of the first two examples: a table, {lit}`BEGIN`, a row, an INSERT of the
same key with the algorithm, {lit}`COMMIT` and a query of the names. -/
def failedInsert (algorithm : Option ConflictAlgorithm) : List Syntax.Statement :=
  [createT, .begin, insertT "1" "a", insertT "1" "b" algorithm, .commit, selectNames]

/-- {lit}`SELECT c FROM t`. -/
def selectAdded : Syntax.Statement :=
  .select [.expression (.identifier (name! "c") .none) none ""] (some { table := name! "t", alias := none })
    [] none [] [] none none

/-- {lit}`ALTER TABLE t ADD COLUMN c` with the constraints. -/
def addColumnC (constraints : List ColumnConstraint) : Syntax.Statement :=
  .addColumn (name! "t") { name := name! "c", declaredType := some "INTEGER", constraints }

end Belay.Sqlite.Model.Conformance.RunPassExamples
