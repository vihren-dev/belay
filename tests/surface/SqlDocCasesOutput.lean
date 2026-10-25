import Belay

set_option doc.verso true

/-! Cases of the {lit}`sql` documentation block for what a block observes: the rendered text of the
results, the typed outputs, alternative results and the clock. -/

open Belay.Sqlite

def start : Database := db! r"CREATE TABLE t(x INTEGER); INSERT INTO t VALUES(1)"
def names : Database := db! r"CREATE TABLE m(name); INSERT INTO m VALUES('b'); INSERT INTO m VALUES('a')"
def sameText : Database := db! r"CREATE TABLE m(x); INSERT INTO m VALUES(1); INSERT INTO m VALUES('1')"
def noon : Env := clockAt "2026-10-20 12:00:00"
def nullOutputs : List Output := [.rows [[.null]]]
def textOutputs : List Output := [.rows [["NULL"]]]
def writeThenRows : List Output := [.done 1, .done 1, .rows [[7]]]
def separateSets : List Output := [.rows [[1]], .rows [[2]]]
def oneSet : List Output := [.rows [[1], [2]]]
def noRows : List Output := [.rows []]
def alternatives : List Output := [.oneOf [[[1]], [["1"]]]]

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

--! case typed-null
/-- A typed expectation separates NULL from text.
```sql (db := start) (expected := nullOutputs)
SELECT NULL;
```
-/
def typedNull : Unit := ()

--! case typed-null-is-not-text
--! error 4:0 expected outputs: [rows [["NULL"]]]
/-- The typed expectation of the text NULL rejects a NULL.
```sql (db := start) (expected := textOutputs)
SELECT NULL;
```
-/
def typedNullIsNotText : Unit := ()

--! case typed-write-count-and-boundaries
/-- A typed expectation states write counts and the end of each result set.
```sql (db := start) (expected := writeThenRows)
INSERT INTO t VALUES (9);
UPDATE t SET x = 7 WHERE x = 9;
SELECT x FROM t WHERE x = 7;
```
-/
def typedWriteCount : Unit := ()

--! case typed-separates-result-sets
/-- The text of separate result sets equals the text of one set; typed outputs differ.
```sql (db := start) (expected := separateSets)
SELECT 1;
SELECT 2;
```
-/
def typedSeparateSets : Unit := ()

--! case typed-one-set-is-not-two-sets
--! error 4:0 actual outputs: [rows [[1], [2]]]
/-- One result set with two rows is not two result sets.
```sql (db := start) (expected := separateSets)
SELECT 1 UNION ALL SELECT 2;
```
-/
def typedOneSet : Unit := ()

--! case typed-empty-result
/-- An empty result set is an output, and the text does not show it.
```sql (db := start) (expected := noRows)
SELECT x FROM t WHERE x = 5;
```
-/
def typedEmptyResult : Unit := ()

--! case typed-comments-stay-sql
/-- All comments of a typed block are SQL, so a trailing line comment does not state text.
```sql (db := start) (expected := nullOutputs)
SELECT NULL;
-- this comment is not an expectation
```
-/
def typedCommentsStaySql : Unit := ()

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

--! case typed-alternatives-are-compared-whole
/-- A typed expectation states the alternatives themselves.
```sql (db := sameText) (expected := alternatives)
SELECT x FROM m LIMIT 1;
```
-/
def typedAlternatives : Unit := ()

--! case typed-first-alternative-alone-fails
--! error 4:0 actual outputs: [oneOf
/-- The first alternative alone is not the output.
```sql (db := sameText) (expected := nullOutputs)
SELECT x FROM m LIMIT 1;
```
-/
def typedFirstAlternative : Unit := ()

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
