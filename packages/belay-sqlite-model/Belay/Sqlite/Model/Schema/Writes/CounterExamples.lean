import Belay.Sqlite.Model.Queries.Preparation.ScriptRunExamples
import Belay.Sqlite.Model.Schema.Writes.ScriptRunExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.CounterExamples

open Belay.Sqlite.Model Syntax

/-- {lit}`INSERT INTO t VALUES (5, 'a'), (9, 'b')`. -/
def insertTwo : Syntax.Statement :=
  .insert (name! "t") none [[.numeric "5", .string "a".toUTF8.toList], [.numeric "9", .string "b".toUTF8.toList]] [] none

/-- {lit}`INSERT INTO t VALUES (3, 'x'), (5, 'y')`: the second row has a rowid that the table
holds after {name}`insertTwo`. -/
def insertFailing : Syntax.Statement :=
  .insert (name! "t") none [[.numeric "3", .string "x".toUTF8.toList], [.numeric "5", .string "y".toUTF8.toList]] [] none

/-- {lit}`UPDATE t SET name = 'z'`. -/
def updateAll : Syntax.Statement := .update (name! "t") [(name! "name", .string "z".toUTF8.toList)] none []

/-- {lit}`DELETE FROM t WHERE id = 5`. -/
def deleteFive : Syntax.Statement := .delete (name! "t") (some (.compare .eq (.identifier (name! "id") .none) (.numeric "5"))) []

/-- {lit}`INSERT INTO t VALUES (5, 'q') ON CONFLICT(id) DO UPDATE SET name = 'q'`: the row
conflicts with the row 5 that {name}`insertTwo` stored. -/
def upsertUpdate : Syntax.Statement :=
  .insert (name! "t") none [[.numeric "5", .string "q".toUTF8.toList]]
    [{ target := some [name! "id"], action := .update [(name! "name", .string "q".toUTF8.toList)] none }] none

/-- {lit}`INSERT INTO t VALUES (5, 'q'), (11, 'n') ON CONFLICT DO NOTHING`: the first row
conflicts with the row 5 that {name}`insertTwo` stored. -/
def upsertSkipping : Syntax.Statement :=
  .insert (name! "t") none [[.numeric "5", .string "q".toUTF8.toList], [.numeric "11", .string "n".toUTF8.toList]]
    [{ target := none, action := .nothing }] none

end Belay.Sqlite.Model.CounterExamples
