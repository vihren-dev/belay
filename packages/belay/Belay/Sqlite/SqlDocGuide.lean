import Belay.Sqlite.DbBang
import Belay.Sqlite.Env
import Belay.Sqlite.SqlDocBlock

set_option doc.verso true

namespace Belay.Sqlite.SqlDoc.Guide

open Belay.Sqlite

/-- A database with one table and one row, which the examples of the guide start from. -/
def start : Database :=
  db! r"CREATE TABLE t(x INTEGER); INSERT INTO t VALUES(1)"

/-- A database with a table whose rows must be positive, for the examples of expected failures. -/
def positive : Database :=
  db! r"CREATE TABLE p(x INTEGER NOT NULL CHECK (x > 0))"

/-- A fixed environment for the examples that read the clock. -/
def noon : Env :=
  clockAt "2026-10-20 12:00:00"

/-- The exact outputs of a script that reads NULL and then the text {lit}`NULL`. -/
def nullThenText : List Output :=
  [.rows [[.null]], .rows [["NULL"]]]

/-! How to check SQL examples in documentation. Write the example as a {lit}`sql` code block in a
docstring, in a file with {lit}`set_option doc.verso true` that imports {lit}`Belay`. Lean runs
the SQL while it elaborates the file, and an example that does not do what its text says is an
error at the block.

The header {lit}`(db := start)` names the database. It is a closed definition, and each block
starts from its own copy, so an example never sees the changes of an earlier example. The
statements run in order. The trailing {lit}`--` lines state the expected text: the cells of each
row joined by {lit}` | `, and the rows joined by newlines. A write count is not part of the text.

```sql (db := start)
UPDATE t SET x = 7;
SELECT x FROM t;
-- 7
```

The expected text is the last group of lines that start with {lit}`--`. A {lit}`--` inside a string
or a quoted name does not start a comment, and an earlier comment is part of the SQL. Remove one
space after the marker, and no more. If you do not give an expected text, the block expects no
text at all.

# Parameters

A header argument binds the parameter of the same name. {lit}`:v`, {lit}`@v` and {lit}`$v` need
the argument {lit}`(v := 5)`; {lit}`?` and {lit}`?2` need {lit}`(p1 := ...)` and {lit}`(p2 := ...)`.
A number or a double-quoted string gives an integer or a text. A name of a closed {lit}`Value`
definition gives that value. Every parameter needs a value, and every argument must bind a
parameter.

```sql (db := start) (v := 5)
UPDATE t SET x = :v;
SELECT x FROM t;
-- 5
```

When a parameter has the name of a header option, such as {lit}`:db`, bind every parameter of a
block with {lit}`(values := lists)`. It names a closed list with one list of values for each
statement. Each list has one value for each number from 1 to the largest number of the statement.

# Exact outputs

The text of a block cannot tell {lit}`NULL` from the text {lit}`'NULL'`, and it cannot show where
one result set ends and the next starts. {lit}`(expected := outputs)` names a closed
{lit}`List Output` that states every output exactly. It takes the place of the comment lines, and
all comments of the block stay in the SQL.

```sql (db := start) (expected := nullThenText)
SELECT NULL;
SELECT 'NULL';
```

# Expected failures

The flag {lit}`+error` expects the first failing statement to fail, and the comment lines state
the message of SQLite. A block without {lit}`+error` that fails is an error, and so is a block
with {lit}`+error` that succeeds. The model must be able to run the statement: a statement that
the model does not run is an error of the block, also with {lit}`+error`.

```sql (db := positive) +error
INSERT INTO p VALUES (0);
-- CHECK constraint failed: x > 0
```

# The clock

A statement that reads the clock needs a closed environment, which {lit}`(env := noon)` gives.

```sql (db := start) (env := noon)
SELECT CURRENT_TIMESTAMP;
-- 2026-10-20 12:00:00
```
-/

end Belay.Sqlite.SqlDoc.Guide
