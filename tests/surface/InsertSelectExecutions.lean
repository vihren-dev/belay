import Belay

/-! A fixture module of `tests/surface_execution_test.py`: INSERT from a query has one execution for
each order in which SQLite may read its source (ADR 0019, D4), and a claim about the statement is a
claim about all of them. The source table {lit}`s` has an index on {lit}`x`, so a query on {lit}`x`
may be answered by the scan or by the index. The scan gives the rowids 1 and 2 to the values 20 and 10;
the index gives them to 10 and 20, as native SQLite 3.51.0 does for the filter {lit}`x > 0`. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace InsertSelectExecutionExamples
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The source {lit}`s` with the rows (1, 20) and (2, 10), its index on {lit}`x`, and the empty target
{lit}`t` (the third table of the catalog, at position 2). -/
def sample : Belay.Sqlite.Database := db! r"CREATE TABLE s(id INTEGER PRIMARY KEY, x INTEGER);
  CREATE INDEX sx ON s(x);
  CREATE TABLE t(id INTEGER PRIMARY KEY, name INTEGER);
  INSERT INTO s VALUES (1, 20), (2, 10)"

/-- A fresh context without a clock. -/
def start : ExecutionContext :=
  ExecutionContext.initial sample { clock := none, counters := Counters.newConnection }

/-- A fresh context on a database without tables. -/
def emptyStart : ExecutionContext :=
  ExecutionContext.initial Belay.Sqlite.Database.empty { clock := none, counters := Counters.newConnection }

/-- The copy of the values of {lit}`x` into {lit}`t`. -/
def copy : Sql (List Output) := send (sql r"INSERT INTO t(name) SELECT x FROM s WHERE x > 0")

/-- The names in the rows of {lit}`t` in scan order. -/
def names (state : ExecutionContext) : List Value :=
  (state.connection.state.database.rowsAt 2).map (·.values.getD 1 .null)

/-- The claim that holds for each execution: the copy succeeds, and {lit}`t` holds the two values in
some order. -/
theorem every_execution_has_both_values :
    copy.andOk (fun _ state => names state = [.integer 20, .integer 10] ∨ names state = [.integer 10, .integer 20])
      start := by decide +kernel

/-- A claim about the order of the rows is false: the execution that reads the index gives the rowid 1
to the value 10, so "the first row holds 20" does not hold for every execution. -/
theorem first_row_claim_fails :
    ¬ copy.andOk (fun _ state => (names state).head? = some (.integer 20)) start := by decide +kernel

/-- The claim that the first row holds 20 is not refuted by the model's own execution alone: the
claim for the execution that reads the scan holds, so the failure above is due to the other
execution. The claim over the weaker postcondition "the first row holds 20 or 10" holds. -/
theorem first_row_is_a_value :
    copy.andOk (fun _ state => (names state).head? = some (.integer 20) ∨ (names state).head? = some (.integer 10))
      start := by decide +kernel

set_option sql.orderWarnings false in
/-- A script in which one execution fails and the other succeeds. The source rows are 5 and the smallest
integer. The scan reaches 5 and stops at the limit. The index reaches the smallest integer first, and
{lit}`abs` of it is an integer overflow (native SQLite 3.51.0 gives both results). -/
def limited : Sql (List Output) :=
  send (sql r"CREATE TABLE s(id INTEGER PRIMARY KEY, x INTEGER);
    CREATE INDEX sx ON s(x);
    CREATE TABLE t(id INTEGER PRIMARY KEY);
    INSERT INTO s VALUES (1, 5), (2, -9223372036854775808);
    INSERT INTO t SELECT abs(x) FROM s WHERE x < 100 LIMIT 1")

/-- The script does not succeed: one of its executions ends with an error. -/
theorem some_execution_fails :
    ¬ limited.SucceedsFrom none 0 emptyStart.connection := by
  decide +kernel

/-- The copy without a limit succeeds in every execution. -/
theorem copy_succeeds : copy.SucceedsFrom none 0 start.connection := by decide +kernel

#print axioms every_execution_has_both_values
#print axioms first_row_claim_fails
#print axioms first_row_is_a_value
#print axioms some_execution_fails
#print axioms copy_succeeds

end InsertSelectExecutionExamples
