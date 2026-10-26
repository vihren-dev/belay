import Belay.Sqlite.Model.InsertSelectExamples

set_option doc.verso true

/-! Examples of the faults of the query of INSERT from a query that the model does not describe (ADR 0019, D4,
amended 2026-10-25), checked by {lit}`#guard` when the package builds: a fault of reading the source rows
themselves, and a window whose parameter makes the query a scan only after the binding. -/

namespace Belay.Sqlite.Model.InsertSelectExamples

open Belay.Sqlite.Model Syntax Resolution.Examples ScriptRunExamples

/-- {lit}`INSERT INTO t(name) SELECT 1 FROM json_each('bad')`: a query over a source that fails when it
reads the JSON text. -/
def copyFromBadJson : Syntax.Statement :=
  .insertSelect (name! "t") (some [name! "name"])
    { columns := [.expression (.numeric "1") none "1"],
      source := some { table := name! "json_each", alias := none, arguments := some [.string "bad".toUTF8.toList] },
      joins := [], filter := none, groupBy := [], orderBy := [], limit := none, offset := none } []

-- SQLite reports malformed JSON for the source. The model does not describe a fault of the source, so the
-- statement ends the run as a statement that the model does not run.
#guard (allOutputs (plainSource ++ [createTarget, copyFromBadJson])).map (·.getLast?.map Output.endsRun) == [some true]

/-- {lit}`INSERT INTO t(name) SELECT abs(x) FROM s LIMIT 1 OFFSET ?1`. -/
def copyAbsAfterOffset : Syntax.Statement :=
  .insertSelect (name! "t") (some [name! "name"])
    { columns := [.expression (.call "abs" [.identifier (name! "x") .none]) none "abs"],
      source := some { table := name! "s", alias := none }, joins := [], filter := none,
      groupBy := [], orderBy := [], limit := some (.numeric "1"), offset := some (.parameter 1) } []

-- The rows of the source are the smallest integer and 5. With the offset 1 SQLite skips the first row and
-- copies abs(5) without reading abs of the smallest integer; the model has no description of the window
-- skipping a failing row, so the statement ends the run as a statement that the model does not run. A
-- literal offset is the same query.
#guard (allOutputs (plainSource ++ [createTarget, insertParameter, insertParameter, copyAbsAfterOffset])
    [[], [], [.integer (-9223372036854775808)], [.integer 5], [.integer 1]]).map (·.getLast?.map Output.endsRun) == [some true]

end Belay.Sqlite.Model.InsertSelectExamples
