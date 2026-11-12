import Belay

set_option doc.verso true

/-! Cases of the {lit}`sql` documentation block for the expected-text lines and for the position
of errors in the original file: quoted and commented {lit}`--`, indentation, characters outside
the Basic Multilingual Plane, and line ends. The test elaborates this file also with Windows
line ends. -/

open Belay.Sqlite

/-- A database with one table and the row 1, which every case starts from. -/
def start : Database := db! r"CREATE TABLE t(x INTEGER); INSERT INTO t VALUES(1)"

--! case marker-inside-a-string-is-sql
/-- A line that starts inside a string literal is not a comment.
```sql (db := start)
SELECT 'x
-- y';
-- x
-- -- y
```
-/
def markerInString : Unit := ()

--! case marker-inside-a-block-comment-is-sql
/-- A line inside a block comment is not a comment line of its own.
```sql (db := start)
/*
-- not expected
*/
SELECT 1;
-- 1
```
-/
def markerInBlockComment : Unit := ()

--! case unclosed-block-comment-hides-the-expectation
--! error 4:0 expected text: ""
/-- An unclosed block comment runs to the end, so no expected text remains.
```sql (db := start)
SELECT 1;
/*
-- 1
```
-/
def unclosedBlockComment : Unit := ()

--! case earlier-line-comment-stays-sql
/-- Only the last group of comment lines is the expectation.
```sql (db := start)
-- A comment before the query.
SELECT 1;
-- This comment is between two statements.
SELECT 2;
-- 1
-- 2
```
-/
def earlierComment : Unit := ()

--! case comment-after-sql-is-not-expected
--! error 4:0 expected text: ""
/-- A comment on the line of a statement is a comment of the SQL.
```sql (db := start)
SELECT 1; -- 1
```
-/
def commentAfterSql : Unit := ()

--! case blank-and-spaced-expected-lines
/-- A marker without text gives an empty line, one space after a marker is removed and no more, and
white space lines after the group are ignored.
```sql (db := start)
SELECT 'a' || char(10) || char(10) || '  b';
-- a
--
--   b

```
-/
def blankExpectedLines : Unit := ()

--! case trigger-body-comments-stay-sql
/-- A comment line inside a trigger body is part of the statement.
```sql (db := start)
CREATE TRIGGER g AFTER INSERT ON t BEGIN
-- a comment line of the trigger
  SELECT 1;
END;
SELECT x FROM t;
-- 1
```
-/
def triggerBody : Unit := ()

--! case non-bmp-characters-in-expected-text
/-- Characters outside the Basic Multilingual Plane keep their form in the expected text.
```sql (db := start)
SELECT 'é😀';
-- é😀
```
-/
def nonBmpText : Unit := ()

--! case error-column-after-non-bmp-characters
--! error 4:12 no such column: nmae
/-- The column of an error counts Unicode characters of the original line.
```sql (db := start)
SELECT '😀', nmae FROM t;
```
-/
def nonBmpColumn : Unit := ()

--! case error-in-a-nested-indented-block
--! error 7:10 no such column: nmae
/-- A fenced block in a list item is indented, and the error is in the original columns.

 * An item.

   ```sql (db := start)
   SELECT nmae FROM t;
   ```
-/
def nestedBlock : Unit := ()

--! case mismatch-in-a-nested-indented-block
--! error 7:0 expected text: "2"
/-- A mismatch in an indented block is at the start of the first line of its body.

 * An item.

   ```sql (db := start)
   SELECT 1;
   -- 2
   ```
-/
def nestedMismatch : Unit := ()

--! case error-on-a-later-line
--! error 7:7 no such column: nmae
/-- The line of an error is the line of its statement in the file.
```sql (db := start)
SELECT 1;

SELECT 2,
       nmae FROM t;
-- 1
```
-/
def laterLine : Unit := ()
