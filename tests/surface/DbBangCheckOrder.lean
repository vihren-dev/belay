import Belay

/-! A fixture of `tests/surface_guide_test.py`: `db! r"..."` names the NOT NULL column or the
`STRICT` column that a write fails in SQLite 3.51's order of checks (`columnFailures` of
`Model/RowCheckOrder.lean`, through `failingConstraints` of `Model/FailingConstraints.lean`). A
table without a generated column checks NOT NULL first; a table with a generated column checks
the types first, the columns that are not generated before the generated ones in each check.
Each expected message has SQLite's text as the native `sqlite3` shell 3.51 gives it for the same
SQL. `#guard_msgs (positions := true)` checks each message and its position as
`@ +line:start...stop`, with the line from the command and columns from 0. The file fails to
elaborate when a message or a position is not the expected one. -/

open Belay.Sqlite

-- Without a generated column: NOT NULL before the type, for INSERT and UPDATE.
/--
@ +3:2...34
error: NOT NULL constraint failed: i.b; correct the row, or the statement that writes it
---
@ +5:2...32
error: NOT NULL constraint failed: i.b; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def plainOrder : Database := db! r#"
  CREATE TABLE i (a INT, b INT NOT NULL) STRICT;
  INSERT INTO i VALUES ('x', NULL);
  INSERT INTO i VALUES (1, 1);
  UPDATE i SET a = 'x', b = NULL;"#

-- With a generated column: the type of an ordinary column, then the type of a generated column,
-- then NOT NULL of an ordinary column, then NOT NULL of a generated column, then CHECK.
/--
@ +3:2...32
error: cannot store TEXT value in INT column t.b; correct the row, or the statement that writes it
---
@ +5:2...33
error: cannot store TEXT value in INT column p.a; correct the row, or the statement that writes it
---
@ +7:2...32
error: cannot store TEXT value in INT column q.z; correct the row, or the statement that writes it
---
@ +9:2...42
error: NOT NULL constraint failed: u.b; correct the row, or the statement that writes it
---
@ +11:2...30
error: NOT NULL constraint failed: v.a; correct the row, or the statement that writes it
---
@ +14:2...32
error: cannot store TEXT value in INT column r.z; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def generatedOrder : Database := db! r#"
  CREATE TABLE t (a INT AS (NULL) NOT NULL, b INT) STRICT;
  INSERT INTO t (b) VALUES ('x');
  CREATE TABLE p (z INT NOT NULL, a INT AS ('q')) STRICT;
  INSERT INTO p (z) VALUES (NULL);
  CREATE TABLE q (a INT AS ('q'), z INT) STRICT;
  INSERT INTO q (z) VALUES ('x');
  CREATE TABLE u (a INT AS (w) NOT NULL, b INT NOT NULL, w INT);
  INSERT INTO u (b, w) VALUES (NULL, NULL);
  CREATE TABLE v (a INT AS (NULL) NOT NULL, b INT CHECK (b > 0));
  INSERT INTO v (b) VALUES (0);
  CREATE TABLE r (z INT, y INT NOT NULL, a INT AS (z)) STRICT;
  INSERT INTO r VALUES (1, 1);
  UPDATE r SET z = 'x', y = NULL;"#
