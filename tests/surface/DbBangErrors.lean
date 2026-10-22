import Belay

/-! A fixture of `tests/surface_guide_test.py`: `db! r"..."` (`Belay/Sqlite/DbBang.lean`,
`Belay/Sqlite/DbDiagnostics.lean`) shows each error of the SQL text at its position in the text,
and a failed `db!` gives no second error where it is used. `#guard_msgs (positions := true)`
checks each message and its position as `@ +line:start...stop`, with the line from the command
and columns from 0. The file fails to elaborate when a message or a position is not the expected
one. -/

open Belay.Sqlite

-- A NOT NULL column without a value: an error at the statement. The model does not keep the
-- constraint that fails, so the message says that it does not name it.
/--
@ +8:2...49
error: constraint failed; the model does not name the constraint that fails. Run the statement in the sqlite3 shell to see SQLite's message
-/
#guard_msgs (positions := true) in
def notNullMissing : Database := db! r"
  CREATE TABLE invoices (
    id INTEGER PRIMARY KEY,
    customer TEXT NOT NULL,
    amount INTEGER NOT NULL CHECK (amount >= 0),
    status TEXT NOT NULL DEFAULT 'open'
  );
  INSERT INTO invoices (id, amount) VALUES (3, 5);"

-- A PRIMARY KEY conflict: an error at the statement. The run goes on after it, so each
-- statement that fails shows its error.
/--
@ +1:68...97
error: constraint failed; the model does not name the constraint that fails. Run the statement in the sqlite3 shell to see SQLite's message
---
@ +1:114...116
error: table t has no column named zz
-/
#guard_msgs (positions := true) in
def keyConflict : Database := db! r"CREATE TABLE t (a PRIMARY KEY); INSERT INTO t VALUES (1), (1); INSERT INTO t (zz) VALUES (1)"

-- A prepare error: SQLite's message, at the name.
/--
@ +1:72...74
error: table t has no column named zz
-/
#guard_msgs (positions := true) in
def prepareError : Database := db! r"CREATE TABLE t (a); INSERT INTO t (zz) VALUES (1)"

-- A model restriction: the model's reason, at the node. The run ends there, so the statement
-- after it shows no error.
/--
@ +1:65...70
error: the rowid names rowid, _rowid_ and oid are not modeled in expressions over a table, or as the SET column of a table without an INTEGER PRIMARY KEY; name the table's columns
-/
#guard_msgs (positions := true) in
def restricted : Database := db! r"CREATE TABLE t (a); SELECT a, rowid FROM t; INSERT INTO t (zz) VALUES (1)"

-- A statement that reads the clock ends the run: an error at the statement, and none after it.
/--
@ +1:50...74
error: the statement reads the clock, which this run does not describe; write the time as a literal value
-/
#guard_msgs (positions := true) in
def clock : Database := db! r"CREATE TABLE t (a); SELECT CURRENT_TIMESTAMP; INSERT INTO t (zz) VALUES (1)"

-- SQL that SQLite's grammar rejects, at the offset where it rejects it.
/--
@ +1:56...57
error: SQLite's grammar rejects the SQL at this offset; correct the SQL there and run the command again
-/
#guard_msgs (positions := true) in
def syntaxError : Database := db! r"CREATE TABLE t (a); SELEC 1"

-- A form that the translation refuses, at the statement.
/--
@ +1:52...58
error: This statement is not modeled; the model runs CREATE TABLE, CREATE INDEX, CREATE TRIGGER, ALTER TABLE ADD COLUMN, DROP TABLE, DROP INDEX, DROP TRIGGER, BEGIN, COMMIT, ROLLBACK, INSERT, UPDATE, DELETE, SELECT and PRAGMA foreign_keys
-/
#guard_msgs (positions := true) in
def refused : Database := db! r"CREATE TABLE t (a); VACUUM"

-- A text that leaves a transaction open: an error at the end of the text, the closing quote.
/--
@ +1:85...86
error: the text of db! leaves a transaction open at its end; end the transaction with COMMIT, or remove its BEGIN
-/
#guard_msgs (positions := true) in
def openAtEnd : Database := db! r"CREATE TABLE t (a); BEGIN; INSERT INTO t VALUES (1)"

-- A run that ends early does not report an open transaction: the statements after the end do
-- not run, and here the COMMIT after the clock read ends the transaction.
/--
@ +1:69...93
error: the statement reads the clock, which this run does not describe; write the time as a literal value
-/
#guard_msgs (positions := true) in
def endsInTransaction : Database := db! r"CREATE TABLE t (a); BEGIN; SELECT CURRENT_TIMESTAMP; COMMIT"

-- A failed `db!` is a `Database`, and `sql!` on it gives no second error.
example : Database := keyConflict

#guard_msgs (positions := true) in
def onFailedDb : Script := sql! keyConflict r"SELECT a FROM t"

-- A transaction that the text ends with COMMIT builds the database.
/-- A table with one row, written in a transaction. -/
def committed : Database := db! r"CREATE TABLE t (a NOT NULL PRIMARY KEY); BEGIN; INSERT INTO t VALUES (1); COMMIT"

example : committed.rows "t" = some [[1]] := by decide +kernel
