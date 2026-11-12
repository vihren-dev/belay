import Belay

set_option doc.verso true

/-! Cases of the {lit}`sql` documentation block for failures: which SQL failures a block can
expect with {lit}`+error`, and which errors stay errors of the file. -/

open Belay.Sqlite

/-- A database with a unique column and the row 1, so that a second 1 fails. -/
def start : Database := db! r"CREATE TABLE t(x INTEGER UNIQUE); INSERT INTO t VALUES(1)"
/-- The exact outputs of one query that returns 1, which a block with a failure cannot have. -/
def outputsOfOne : List Output := [.rows [[1]]]

--! case prepare-error-is-an-expected-failure
/-- A column that does not exist fails when SQLite prepares the statement.
```sql (db := start) +error
SELECT nmae FROM t;
-- no such column: nmae
```
-/
def prepareFailure : Unit := ()

--! case runtime-error-is-an-expected-failure
/-- A duplicate key fails when SQLite runs the statement.
```sql (db := start) +error
INSERT INTO t VALUES (2);
INSERT INTO t VALUES (1);
-- UNIQUE constraint failed: t.x
```
-/
def runtimeFailure : Unit := ()

--! case syntax-error-is-an-expected-failure
/-- The parser reports the offset, and the model has no other text for a syntax error.
```sql (db := start) +error
SELEC 1;
-- SQLite's grammar rejects the SQL at this offset; correct the SQL there and run the command again
```
-/
def syntaxFailure : Unit := ()

--! case wrong-expected-message
--! error 4:0 SQL error mismatch
/-- The expected message is not the message of SQLite.
```sql (db := start) +error
INSERT INTO t VALUES (1);
-- UNIQUE constraint failed: t.y
```
-/
def wrongMessage : Unit := ()

--! case unexpected-success-with-error-flag
--! error 4:0 ran without an error
/-- A block with +error needs a failing statement.
```sql (db := start) +error
SELECT x FROM t;
-- no such column: x
```
-/
def unexpectedSuccess : Unit := ()

--! case unexpected-failure-without-error-flag
--! error 4:7 no such column: nmae
/-- A failing statement without +error is an error at the statement.
```sql (db := start)
SELECT nmae FROM t;
-- 1
```
-/
def unexpectedFailure : Unit := ()

--! case runtime-failure-is-at-its-statement
--! error 5:0 UNIQUE constraint failed: t.x
/-- The error is at the failing statement and not at the first statement.
```sql (db := start)
INSERT INTO t VALUES (2);
INSERT INTO t VALUES (1);
```
-/
def failureAtStatement : Unit := ()

--! case restriction-is-an-error-with-error-flag
--! error 4:0 This statement is not modeled
/-- A statement outside the model is not an expected SQLite failure.
```sql (db := start) +error
VACUUM;
-- anything
```
-/
def restriction : Unit := ()

--! case unknown-flag-is-a-header-error
--! error 3:21 only the flag +error
/-- Only the flag +error exists.
```sql (db := start) +errors
SELECT 1;
```
-/
def unknownFlag : Unit := ()

--! case positional-argument-is-a-header-error
--! error 3:21 takes named arguments
/-- The header has named arguments and flags only.
```sql (db := start) start
SELECT 1;
```
-/
def positionalArgument : Unit := ()

--! case typed-outputs-with-error-flag
--! error 3:21 +error expects a failure
/-- Typed outputs state a block that succeeds.
```sql (db := start) (expected := outputsOfOne) +error
SELECT 1;
```
-/
def typedWithError : Unit := ()

--! case broken-database-gives-no-cascading-error
--! error 2:51 SQLite's grammar rejects
def brokenDatabase : Database := db! r"CREATE TABLE"

/-- A database definition that fails has its own error, and the block adds none.
```sql (db := brokenDatabase)
SELECT 1;
-- 1
```
-/
def brokenDatabaseBlock : Unit := ()
