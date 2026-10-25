import Belay

set_option doc.verso true

/-! Cases of the {lit}`sql` documentation block for typed expectations of the complete outputs. -/

open Belay.Sqlite

/-- A database with one table and the row 1, which most cases start from. -/
def start : Database := db! r"CREATE TABLE t(x INTEGER); INSERT INTO t VALUES(1)"

/-- A database with the rows 1 and '1', which differ in type and render alike. -/
def sameText : Database := db! r"CREATE TABLE m(x); INSERT INTO m VALUES(1); INSERT INTO m VALUES('1')"

/-- The exact outputs of one query that returns NULL. -/
def nullOutputs : List Output := [.rows [[.null]]]

/-- The exact outputs of one query that returns the text NULL. -/
def textOutputs : List Output := [.rows [["NULL"]]]

/-- The outputs of two writes and then one query that returns 7. -/
def writeThenRows : List Output := [.done 1, .done 1, .rows [[7]]]

/-- The outputs of two queries that return one row each. -/
def separateSets : List Output := [.rows [[1]], .rows [[2]]]

/-- The outputs of one query that returns no row. -/
def noRows : List Output := [.rows []]

/-- The outputs of a query whose first row can be 1 or the text 1. -/
def alternatives : List Output := [.oneOf [[[1]], [["1"]]]]

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

