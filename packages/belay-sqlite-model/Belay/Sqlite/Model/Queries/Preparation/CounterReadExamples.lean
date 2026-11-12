import Belay.Sqlite.Model.Shared.Syntax.Syntax

set_option doc.verso true

namespace Belay.Sqlite.Model.CounterReadExamples

open Belay.Sqlite.Model Syntax

/-- {lit}`INSERT INTO t VALUES (changes(), 'x')` after two rows: the new row has the value from
before the statement, 2. -/
def insertReadingChanges : Syntax.Statement :=
  .insert (name! "t") none [[.call "changes" [], .string "x".toUTF8.toList]] []

/-- {lit}`SELECT id FROM t WHERE name = 'x'`: the rowid of the row of {name}`insertReadingChanges`. -/
def selectIdOfX : Syntax.Statement :=
  .select [.expression (.identifier (name! "id") .none) none ""] (some { table := name! "t", alias := none })
    [] (some (.compare .eq (.identifier (name! "name") .none) (.string "x".toUTF8.toList))) [] [] none none

end Belay.Sqlite.Model.CounterReadExamples
