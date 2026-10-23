import Belay

/-! A fixture of `tests/surface_guide_test.py`: `db! r"..."` names the constraint that a write
fails in SQLite 3.51's order of checks (`Model/RowCheckOrder.lean`, `tableFailures` of
`Model/TableFailure.lean` and `changedRowFailures` of `Model/UpdateFailure.lean`, through
`failingConstraints` of `Model/FailingConstraints.lean`). A table without a generated column
checks NOT NULL first; a table with a generated column checks the types of its ordinary and
`VIRTUAL` columns first. The late type check, of the `STORED` columns or of every column of a
table without a generated column, comes before CHECK, or after the rowid in a table without a
CHECK constraint.
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

-- With a generated column, here each `VIRTUAL`: the type of an ordinary column, then the type of a
-- generated column, then NOT NULL of an ordinary column, then NOT NULL of a generated column, then
-- CHECK.
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

-- SQLite's late type check: the types of the `STORED` columns, or of every column in a table
-- without a generated column. It comes after NOT NULL, just before CHECK in a table with a CHECK
-- constraint, and after the rowid, before the unique keys, in a table without one.
/--
@ +3:2...34
error: NOT NULL constraint failed: p1.z; correct the row, or the statement that writes it
---
@ +5:2...31
error: cannot store TEXT value in INT column pe.s; correct the row, or the statement that writes it
---
@ +8:2...37
error: cannot store TEXT value in INT column pf.s; correct the row, or the statement that writes it
---
@ +11:2...38
error: UNIQUE constraint failed: pg.id; correct the row, or the statement that writes it
---
@ +14:2...44
error: cannot store TEXT value in INT column pm.s; correct the row, or the statement that writes it
---
@ +17:2...32
error: UNIQUE constraint failed: a4.id; correct the row, or the statement that writes it
---
@ +20:2...35
error: cannot store TEXT value in INT column a3.w; correct the row, or the statement that writes it
---
@ +24:2...32
error: cannot store TEXT value in INT column a5.w; correct the row, or the statement that writes it
---
@ +27:2...40
error: cannot store TEXT value in INT column a9.z; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def lateTypes : Database := db! r#"
  CREATE TABLE p1 (z INT NOT NULL, a INT AS ('q') STORED) STRICT;
  INSERT INTO p1 (z) VALUES (NULL);
  CREATE TABLE pe (z INT CHECK (z > 5), s INT AS ('q') STORED) STRICT;
  INSERT INTO pe (z) VALUES (1);
  CREATE TABLE pf (z INT UNIQUE, w INT, s INT AS (CASE WHEN w = 1 THEN 'q' ELSE 1 END) STORED) STRICT;
  INSERT INTO pf (z, w) VALUES (1, 0);
  INSERT INTO pf (z, w) VALUES (1, 1);
  CREATE TABLE pg (id INTEGER PRIMARY KEY, w INT, s INT AS (CASE WHEN w = 1 THEN 'q' ELSE 1 END) STORED) STRICT;
  INSERT INTO pg (id, w) VALUES (1, 0);
  INSERT INTO pg (id, w) VALUES (1, 1);
  CREATE TABLE pm (id INTEGER PRIMARY KEY, z INT CHECK (z > 5), w INT, s INT AS (CASE WHEN w = 1 THEN 'q' ELSE 1 END) STORED) STRICT;
  INSERT INTO pm (id, z, w) VALUES (1, 6, 0);
  INSERT INTO pm (id, z, w) VALUES (1, 6, 1);
  CREATE TABLE a4 (id INTEGER PRIMARY KEY, w INT) STRICT;
  INSERT INTO a4 VALUES (1, 0);
  INSERT INTO a4 VALUES (1, 'x');
  CREATE TABLE a3 (id INTEGER PRIMARY KEY, z INT CHECK (z > 5), w INT) STRICT;
  INSERT INTO a3 VALUES (1, 6, 0);
  INSERT INTO a3 VALUES (1, 6, 'x');
  CREATE TABLE a5 (z INT, w INT) STRICT;
  CREATE UNIQUE INDEX a5_z ON a5 (z);
  INSERT INTO a5 VALUES (1, 0);
  INSERT INTO a5 VALUES (1, 'x');
  CREATE TABLE a9 (id INTEGER PRIMARY KEY, z INT, g INT AS (1) VIRTUAL) STRICT;
  INSERT INTO a9 (id, z) VALUES (1, 0);
  INSERT INTO a9 (id, z) VALUES (1, 'x');"#

-- An UPDATE of several rows: a conflict of a changed row depends on SQLite's order of the rows, so
-- the message names the rowid and each failure that the row's checks meet after it. SQLite gives
-- `UNIQUE constraint failed: m.id` for the first UPDATE, in each order of the rows, and `cannot
-- store TEXT value in INT column n.w` for the second.
/--
@ +4:2...28
error: a constraint failed, and SQLite names one of these: "UNIQUE constraint failed: m.id" or "UNIQUE constraint failed: m.z". Which one may depend on the order in which the UPDATE visits the rows, which the model does not keep; correct the row, or the statement that writes it
---
@ +7:2...30
error: a constraint failed, and SQLite names one of these: "UNIQUE constraint failed: n.id" or "cannot store TEXT value in INT column n.w". Which one may depend on the order in which the UPDATE visits the rows, which the model does not keep; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def updateOrder : Database := db! r#"
  CREATE TABLE m (id INTEGER PRIMARY KEY, z UNIQUE);
  INSERT INTO m VALUES (1, 1), (2, 2);
  UPDATE m SET id = 5, z = 7;
  CREATE TABLE n (id INTEGER PRIMARY KEY, w INT) STRICT;
  INSERT INTO n VALUES (1, 0), (2, 0);
  UPDATE n SET id = 5, w = 'x';"#

-- An UPDATE runs only the CHECK constraints that read a changed column. When it runs none, the
-- late type check comes after the rowid, so the message names the rowid. SQLite 3.51 gives these
-- messages, measured with the `sqlite3` shell.
/--
@ +4:2...43
error: UNIQUE constraint failed: t.id; correct the row, or the statement that writes it
---
@ +5:2...50
error: cannot store TEXT value in INT column t.w; correct the row, or the statement that writes it
---
@ +8:2...44
error: UNIQUE constraint failed: q3.id; correct the row, or the statement that writes it
---
@ +11:2...44
error: cannot store TEXT value in INT column q2.e; correct the row, or the statement that writes it
---
@ +14:2...82
error: UNIQUE constraint failed: q5.id; correct the row, or the statement that writes it
---
@ +15:2...89
error: cannot store TEXT value in INT column q5.w; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def updateChecks : Database := db! r#"
  CREATE TABLE t (id INTEGER PRIMARY KEY, c INT CHECK (c > 0), w INT) STRICT;
  INSERT INTO t VALUES (1, 1, 0), (2, 1, 0);
  UPDATE t SET id = 1, w = 'x' WHERE id = 2;
  UPDATE t SET id = 1, w = 'x', c = c WHERE id = 2;
  CREATE TABLE q3 (id INTEGER PRIMARY KEY, w INT, CHECK (1)) STRICT;
  INSERT INTO q3 VALUES (1, 0), (2, 0);
  UPDATE q3 SET id = 1, w = 'x' WHERE id = 2;
  CREATE TABLE q2 (id INTEGER PRIMARY KEY, w ANY, e INT AS (w) STORED CHECK (e IS NOT NULL)) STRICT;
  INSERT INTO q2 (id, w) VALUES (1, 0), (2, 0);
  UPDATE q2 SET id = 1, w = 'x' WHERE id = 2;
  CREATE TABLE q5 (id INTEGER PRIMARY KEY, k INT UNIQUE, c INT CHECK (c > 0), w INT) STRICT;
  INSERT INTO q5 VALUES (1, 1, 1, 0), (2, 2, 1, 0);
  INSERT INTO q5 VALUES (3, 2, 1, 0) ON CONFLICT (k) DO UPDATE SET id = 1, w = 'x';
  INSERT INTO q5 VALUES (3, 2, 1, 0) ON CONFLICT (k) DO UPDATE SET id = 1, w = 'x', c = c;"#
