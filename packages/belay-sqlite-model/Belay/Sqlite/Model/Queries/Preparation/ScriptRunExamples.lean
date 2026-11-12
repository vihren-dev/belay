import Belay.Sqlite.Model.Shared.Execution.ScriptRun
import Belay.Sqlite.Model.Queries.Fixtures.Examples

set_option doc.verso true

namespace Belay.Sqlite.Model.ScriptRunExamples

open Belay.Sqlite.Model Syntax

/-- {lit}`SELECT name FROM t`. -/
def selectNames : Syntax.Statement :=
  .select [.expression (.identifier (name! "name") .none) none ""] (some { table := name! "t", alias := none })
    [] none [] [] none none

/-- {lit}`SELECT expression`, without a table. -/
def selectOf (expression : Expr) : Syntax.Statement :=
  .select [.expression expression none ""] none [] none [] [] none none

/-- {lit}`SELECT b FROM c`. -/
def selectClocked : Syntax.Statement :=
  .select [.expression (.identifier (name! "b") .none) none ""] (some { table := name! "c", alias := none })
    [] none [] [] none none

/-- {lit}`SELECT expression FROM t LIMIT 1`. -/
def firstOf (expression : Expr) : Syntax.Statement :=
  .select [.expression expression none ""] (some { table := name! "t", alias := none }) [] none [] []
    (some (.numeric "1")) none

end Belay.Sqlite.Model.ScriptRunExamples
