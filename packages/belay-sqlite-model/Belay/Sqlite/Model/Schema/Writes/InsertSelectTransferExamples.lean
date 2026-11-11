import Belay.Sqlite.Model.Schema.Writes.InsertSelectExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.InsertSelectExamples

open Belay.Sqlite.Model Syntax

/-- {lit}`CREATE TABLE s(a INTEGER UNIQUE)` and {lit}`CREATE TABLE t(a INTEGER UNIQUE)`: a source and a
target with the same index and no rowid alias, for which SQLite copies the rows under the rowids of the
source ({lit}`INSERT INTO t SELECT * FROM s`). -/
def transferTables : List Syntax.Statement :=
  [.createTable (name! "s") [{ name := name! "a", declaredType := some "INTEGER", constraints := [.unique] }] [],
    .createTable (name! "t") [{ name := name! "a", declaredType := some "INTEGER", constraints := [.unique] }] []]

/-- {lit}`INSERT INTO s VALUES (?1)`. -/
def insertA : Syntax.Statement := .insert (name! "s") none [[.parameter 1]] []

/-- {lit}`INSERT INTO t SELECT * FROM s`. -/
def transfer : Syntax.Statement :=
  .insertSelect (name! "t") none
    { columns := [.star], source := some { table := name! "s", alias := none },
      joins := [], filter := none, groupBy := [], orderBy := [], limit := none, offset := none } []

end Belay.Sqlite.Model.InsertSelectExamples
