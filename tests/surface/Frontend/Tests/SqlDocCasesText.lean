import Belay

set_option doc.verso true

/-! Cases of the {lit}`sql` documentation block for the text of the results: rows, write counts,
NULL and blobs, alternative results, the clock, independent blocks and the retained documentation. -/

open Belay.Sqlite

/-- A database with one table and the row 1, which most cases start from. -/
def start : Database := db! r"CREATE TABLE t(x INTEGER); INSERT INTO t VALUES(1)"

/-- A database whose first row is not fixed by the model: the rows b and a. -/
def names : Database := db! r"CREATE TABLE m(name); INSERT INTO m VALUES('b'); INSERT INTO m VALUES('a')"

/-- A database with the rows 1 and '1', which differ in type and render alike. -/
def sameText : Database := db! r"CREATE TABLE m(x); INSERT INTO m VALUES(1); INSERT INTO m VALUES('1')"

/-- An environment with a fixed clock for the cases that read the time. -/
def noon : Env := clockAt "2026-10-20 12:00:00"

--! case matching-update-then-select
/-- An update, then a query: the write count is not part of the text.
```sql (db := start)
UPDATE t SET x = 7;
SELECT x FROM t;
-- 7
```
-/
def updateThenSelect : Unit := ()

--! case mismatching-expected-value
--! error 4:0 expected text: "8"
/-- The expected value is wrong.
```sql (db := start)
UPDATE t SET x = 7;
SELECT x FROM t;
-- 8
```
-/
def wrongExpectedValue : Unit := ()

--! case mutated-condition
--! error 4:0 actual text: ""
/-- The condition selects no row, so the expected line is wrong.
```sql (db := start)
UPDATE t SET x = 7;
SELECT x FROM t WHERE x = 8;
-- 7
```
-/
def wrongCondition : Unit := ()

--! case several-result-sets
/-- The text joins the rows of all result sets.
```sql (db := start)
SELECT 1, 'two';
SELECT 3;
-- 1 | two
-- 3
```
-/
def severalResultSets : Unit := ()

--! case zero-rows-and-write-only
/-- A query without rows and a script that only writes give no text.
```sql (db := start)
SELECT x FROM t WHERE x = 5;
INSERT INTO t VALUES (2);
```
-/
def noText : Unit := ()

--! case null-and-text-null-render-alike
/-- The text cannot tell NULL from the text NULL.
```sql (db := start)
SELECT NULL;
SELECT 'NULL';
-- NULL
-- NULL
```
-/
def nullLooksLikeText : Unit := ()

--! case blob-and-whitespace-cells
/-- A blob, spaces and a newline in a cell keep their form.
```sql (db := start)
SELECT x'00ff', ' a ', 'x' || char(10) || 'y';
-- x'00ff' |  a  | x
-- y
```
-/
def blobAndSpaces : Unit := ()

--! case equal-alternatives-pass-in-text-mode
/-- The first row of an unordered query can differ, and both alternatives give the same text.
```sql (db := sameText)
SELECT x FROM m LIMIT 1;
-- 1
```
-/
def equalAlternatives : Unit := ()

--! case distinct-alternatives-fail-in-text-mode
--! error 4:0 SQL result mismatch
/-- The first row can be a or b, so one expected text cannot state the result.
```sql (db := names)
SELECT name FROM m LIMIT 1;
-- a
```
-/
def distinctAlternatives : Unit := ()

--! case clock-from-environment
/-- A closed environment gives the clock.
```sql (db := start) (env := noon)
SELECT CURRENT_TIMESTAMP;
-- 2026-10-20 12:00:00
```
-/
def clockFromEnvironment : Unit := ()

--! case clock-without-environment
--! error 4:0 reads the clock
/-- The default environment has no clock, which the model reports.
```sql (db := start)
SELECT CURRENT_TIMESTAMP;
-- 2026-10-20 12:00:00
```
-/
def clockWithoutEnvironment : Unit := ()

--! case blocks-start-from-their-own-database
/-- The first block changes a row and a connection setting.
```sql (db := start)
UPDATE t SET x = 9;
PRAGMA foreign_keys = ON;
SELECT x FROM t;
-- 9
```
The second block starts from its own copy of the database.
```sql (db := start)
SELECT x FROM t;
PRAGMA foreign_keys;
-- 1
-- 0
```
-/
def independentBlocks : Unit := ()

--! case rendering-keeps-the-sql-and-comments
/-- The documentation data keeps the body of a checked block.
```sql (db := start)
SELECT x FROM t; -- not a standalone comment
-- 1
```
-/
def retainedBody : Unit := ()

open Lean Elab Command in
run_cmd do
  let some (.inr doc) ← findInternalDocString? (← getEnv) ``retainedBody
    | throwError "Missing checked documentation data"
  let bodies := doc.text.filterMap fun
    | .code body => some body
    | _ => none
  unless bodies == #["SELECT x FROM t; -- not a standalone comment\n-- 1\n"] do
    throwError "The checked documentation changed its SQL body: {bodies}"
