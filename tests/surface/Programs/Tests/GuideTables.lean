import Belay

/-! A fixture of `tests/surface_guide_test.py`: `#sql db r"..."` (`Belay/Sqlite/SqlCommand.lean`,
the model's `Model/OutputTable.lean`) shows the output of each statement, rows as a table with
the names of the columns, as the user guide's section "A first example" shows it. The file
fails to elaborate when a message is not the expected one. -/

open Belay.Sqlite

/-- The guide's first database: table `invoices` with two open invoices, of 10 and of 0. -/
def shop : Database := db! r"
  CREATE TABLE invoices (
    id INTEGER PRIMARY KEY,
    customer TEXT NOT NULL,
    amount INTEGER NOT NULL CHECK (amount >= 0),
    status TEXT NOT NULL DEFAULT 'open'
  );
  INSERT INTO invoices (id, customer, amount) VALUES (1, 'acme', 10), (2, 'zeta', 0);"

-- The guide's example.
/--
info: id | customer | amount | status
1  | acme     | 10     | open
2  | zeta     | 0      | open
-/
#guard_msgs in
#sql shop r"SELECT * FROM invoices"

-- Each statement has its output: the count of changed rows, the columns of RETURNING with their
-- aliases, an error with its result code, and a query without rows, which shows its names.
/--
info: done 1

id | who
3  | kilo

error 19

id
-/
#guard_msgs in
#sql shop r"UPDATE invoices SET amount = 5 WHERE id = 2;
  INSERT INTO invoices (id, customer, amount) VALUES (3, 'kilo', 1) RETURNING id, customer AS who;
  INSERT INTO invoices (id, customer, amount) VALUES (4, NULL, 1);
  SELECT id FROM invoices WHERE amount > 100"

-- NULL, a REAL, a BLOB and the text of an expression as the column name.
/--
info: NULL | 1.5 | x'0aff' | 'a' || 'b'
NULL | 1.5 | x'0aff' | ab
-/
#guard_msgs in
#sql shop r"SELECT NULL, 1.5, x'0aff', 'a' || 'b'"

-- A result that depends on the row order: each result that SQLite may give.
/--
info: one of 2 results:

customer
acme

customer
zeta
-/
#guard_msgs in
set_option sql.orderWarnings false in
#sql shop r"SELECT customer FROM invoices LIMIT 1"

-- A statement that reads the clock ends the run.
/--
info: unmodeled "the statement reads the clock, which this run does not describe; write the time as a literal value"
-/
#guard_msgs in
#sql shop r"SELECT CURRENT_TIMESTAMP; SELECT 1"

-- SQL that does not parse is an error at its position in the text.
/--
@ +1:19...20
error: SQLite's grammar rejects the SQL at this offset; correct the SQL there and run the command again
-/
#guard_msgs (positions := true) in
#sql shop r"SELECT FROM"
