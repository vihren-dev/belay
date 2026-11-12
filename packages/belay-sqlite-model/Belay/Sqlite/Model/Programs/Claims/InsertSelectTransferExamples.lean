import Belay.Sqlite.Model.Programs.Claims.InsertSelectExamples
import Belay.Sqlite.Model.Schema.Writes.InsertSelectTransferExamples

set_option doc.verso true

/-! Examples of the transfer optimization of INSERT from a query (ADR 0019, D4, amended 2026-10-25),
checked by {lit}`#guard` when the package builds. SQLite copies the rows of {lit}`INSERT INTO t SELECT * FROM s`
under their rowids in the source when both tables have the same index. The model assigns the next rowids
one after the other, so it describes the statement only when the two agree. -/

namespace Belay.Sqlite.Model.InsertSelectExamples

open Belay.Sqlite.Model Syntax

-- Rows 1 and 2 of the source keep their rowids when copied, as the model assigns them, so the statement
-- is described. After a delete in the source, the source rowids 1 and 3 would be kept by SQLite (native
-- 3.51.0) and the model would assign 1 and 2, so the model does not describe the statement.
#guard (allOutputs (transferTables ++ [insertA, insertA, transfer]) [[], [], [.integer 10], [.integer 20]]).map
    (·.getLast?) == [some (.done 2)]
#guard (allOutputs (transferTables ++ [insertA, insertA, insertA,
      .delete (name! "s") (some (.compare .eq (.identifier (name! "a") .none) (.numeric "20"))) [],
      transfer]) [[], [], [.integer 10], [.integer 20], [.integer 30]]).map
    (·.getLast?.map Output.endsRun) == [some true]

end Belay.Sqlite.Model.InsertSelectExamples
