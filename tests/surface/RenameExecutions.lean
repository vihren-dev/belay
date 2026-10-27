import Belay

/-! A fixture module of `tests/surface_execution_test.py`: a rename keeps the rows and the later statements
read the new names (ADR 0019, D4, part 2). The database {lit}`sample` has the table {lit}`t` with two rows and the
view {lit}`v` of the column {lit}`b`. A rename rewrites the view, so a read of the view after the rename
succeeds, and a read of the old name does not. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace RenameExecutionExamples
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The table {lit}`t` with the rows (1, 'p') and (2, 'q'), and the view {lit}`v` of its column {lit}`b`. -/
def sample : Belay.Sqlite.Database := db! r"CREATE TABLE t(a INTEGER PRIMARY KEY, b TEXT);
  INSERT INTO t VALUES (1, 'p'), (2, 'q');
  CREATE VIEW v AS SELECT b FROM t"

/-- A fresh context without a clock. -/
def start : ExecutionContext :=
  ExecutionContext.initial sample { clock := none, counters := Counters.newConnection }

/-- Rename the table and then its column, write a row under the new names and read the view. -/
def renamed : Sql (List Output) :=
  send (sql r"ALTER TABLE t RENAME TO w;
    ALTER TABLE w RENAME COLUMN b TO d;
    INSERT INTO w(d) VALUES ('r');
    SELECT * FROM v")

/-- The two renames and the statements under the new names succeed. -/
theorem renames_then_new_names_succeed : renamed.SucceedsFrom none 0 start.connection := by decide +kernel

/-- The rows of the first table after the script: the two rows of the start and the new row, with the rowids
that they had and the next rowid, so the rename kept every row. -/
def rowsOfFirstTable (state : ExecutionContext) : List (Int × List Value) :=
  (state.connection.state.database.rowsAt 0).map fun row => (row.rowid, row.values)

/-- The rows of the table after the renames and the insert are the rows before and the new row. -/
theorem rows_are_kept :
    renamed.andOk (fun _ state => rowsOfFirstTable state =
      [(1, [.integer 1, .text [112]]), (2, [.integer 2, .text [113]]), (3, [.integer 3, .text [114]])]) start := by
  decide +kernel

/-- A read of the old name of the table does not succeed after the rename. -/
def oldTableName : Sql (List Output) := send (sql r"ALTER TABLE t RENAME TO w; SELECT a FROM t")

theorem old_table_name_fails : ¬ oldTableName.SucceedsFrom none 0 start.connection := by decide +kernel

/-- A read of the old name of the column does not succeed after the rename of the column. -/
def oldColumnName : Sql (List Output) := send (sql r"ALTER TABLE t RENAME COLUMN b TO d; SELECT b FROM t")

theorem old_column_name_fails : ¬ oldColumnName.SucceedsFrom none 0 start.connection := by decide +kernel

/-- A rename to the name of another table fails and the script stops: SQLite refuses the statement. -/
def takenName : Sql (List Output) := send (sql r"CREATE TABLE u(x); ALTER TABLE t RENAME TO u")

theorem taken_name_fails : ¬ takenName.SucceedsFrom none 0 start.connection := by decide +kernel

#print axioms renames_then_new_names_succeed
#print axioms rows_are_kept
#print axioms old_table_name_fails
#print axioms old_column_name_fails
#print axioms taken_name_fails

end RenameExecutionExamples
