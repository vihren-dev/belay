import Belay.Sqlite.Model.Schema.Writes.InsertSelectExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.InsertSelectExamples

open Belay.Sqlite.Model Syntax

/-- {lit}`INSERT INTO t(name) SELECT 1 FROM json_each('bad')`: a query over a source that fails when it
reads the JSON text. -/
def copyFromBadJson : Syntax.Statement :=
  .insertSelect (name! "t") (some [name! "name"])
    { columns := [.expression (.numeric "1") none "1"],
      source := some { table := name! "json_each", alias := none, arguments := some [.string "bad".toUTF8.toList] },
      joins := [], filter := none, groupBy := [], orderBy := [], limit := none, offset := none } []

/-- {lit}`INSERT INTO t(name) SELECT abs(x) FROM s LIMIT 1 OFFSET ?1`. -/
def copyAbsAfterOffset : Syntax.Statement :=
  .insertSelect (name! "t") (some [name! "name"])
    { columns := [.expression (.call "abs" [.identifier (name! "x") .none]) none "abs"],
      source := some { table := name! "s", alias := none }, joins := [], filter := none,
      groupBy := [], orderBy := [], limit := some (.numeric "1"), offset := some (.parameter 1) } []

end Belay.Sqlite.Model.InsertSelectExamples
