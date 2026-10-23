import Belay

/-! A fixture of `tests/surface_guide_test.py`: `db! r"..."` names the constraint that a plain
INSERT or CREATE UNIQUE INDEX fails as SQLite 3.51 does: NOT NULL, the order of the unique keys,
the columns or the index of a key, CHECK labels, STRICT types and the order of the checks of a row
(`constraintMessage` of `Model/ExecutionMessages.lean`, from
`failingConstraints` of `Model/FailingConstraints.lean`, at the statement by
`Belay/Sqlite/DbDiagnostics.lean`). Each expected message has SQLite's text as the native
`sqlite3` shell 3.51 gives it for the same SQL; where SQLite's choice may depend on what the model
does not keep, the message names each candidate, and a comment gives SQLite's text.
`#guard_msgs (positions := true)` checks each message and its position as `@ +line:start...stop`,
with the line from the command and columns from 0. The file fails to elaborate when a message or a
position is not the expected one. -/

open Belay.Sqlite

-- NOT NULL: SQLite names the first NOT NULL column in table order, not in the order of the
-- column list, and the first row of VALUES that fails.
/--
@ +3:2...68
error: NOT NULL constraint failed: people.email; correct the row, or the statement that writes it
---
@ +4:2...87
error: NOT NULL constraint failed: people.email; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def notNullOrder : Database := db! r#"
  CREATE TABLE people (name NOT NULL, email NOT NULL, phone NOT NULL);
  INSERT INTO people (phone, email, name) VALUES (NULL, NULL, 'Ann');
  INSERT INTO people VALUES ('Ann', 'a@x', '1'), ('Bob', NULL, '2'), (NULL, 'c@x', '3');"#

-- UNIQUE: the rowid alias first; of two UNIQUE constraints, the one written last.
/--
@ +4:2...40
error: UNIQUE constraint failed: accounts.id; correct the row, or the statement that writes it
---
@ +7:2...34
error: UNIQUE constraint failed: badges.serial; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def aliasAndUniqueOrder : Database := db! r#"
  CREATE TABLE accounts (id INTEGER PRIMARY KEY, login UNIQUE);
  INSERT INTO accounts VALUES (1, 'ann');
  INSERT INTO accounts VALUES (1, 'ann');
  CREATE TABLE badges (code UNIQUE, serial UNIQUE);
  INSERT INTO badges VALUES (1, 1);
  INSERT INTO badges VALUES (1, 1);"#

-- UNIQUE: a CREATE UNIQUE INDEX before the constraints of the table, the newest index first,
-- and a key declared ON CONFLICT REPLACE after the others, also under OR ABORT.
/--
@ +5:2...35
error: UNIQUE constraint failed: seats.place; correct the row, or the statement that writes it
---
@ +10:2...33
error: UNIQUE constraint failed: codes.right_code; correct the row, or the statement that writes it
---
@ +13:2...45
error: UNIQUE constraint failed: tags.name; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def indexOrder : Database := db! r#"
  CREATE TABLE seats (label UNIQUE, place);
  CREATE UNIQUE INDEX seats_place ON seats (place);
  INSERT INTO seats VALUES ('a', 1);
  INSERT INTO seats VALUES ('a', 1);
  CREATE TABLE codes (left_code, right_code);
  CREATE UNIQUE INDEX codes_z ON codes (left_code);
  CREATE UNIQUE INDEX codes_a ON codes (right_code);
  INSERT INTO codes VALUES (1, 1);
  INSERT INTO codes VALUES (1, 1);
  CREATE TABLE tags (name UNIQUE, slug UNIQUE ON CONFLICT REPLACE);
  INSERT INTO tags VALUES ('x', 'x');
  INSERT OR ABORT INTO tags VALUES ('x', 'x');"#

-- A PRIMARY KEY that is not the rowid alias and a UNIQUE constraint both fail: the catalog
-- does not keep their order, so the message names both. SQLite 3.51 gives
-- `UNIQUE constraint failed: members.number`.
/--
@ +4:2...35
error: a constraint failed, and SQLite names one of these: "UNIQUE constraint failed: members.email" or "UNIQUE constraint failed: members.number". Which one may depend on the place of the PRIMARY KEY among the UNIQUE constraints, which the model does not keep; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def primaryKeyPlace : Database := db! r#"
  CREATE TABLE members (email, number, UNIQUE (email), PRIMARY KEY (number));
  INSERT INTO members VALUES (1, 1);
  INSERT INTO members VALUES (1, 1);"#

-- Keys of several columns in key order, partial indexes on columns, and keys with an
-- expression, which SQLite names by the index; CREATE UNIQUE INDEX on rows that fail it.
/--
@ +4:2...46
error: UNIQUE constraint failed: pairs.y, pairs.x; remove the rows whose values of the index are equal, or change the index
---
@ +5:2...46
error: UNIQUE constraint failed: index 'pairs_e'; remove the rows whose values of the index are equal, or change the index
---
@ +8:2...42
error: UNIQUE constraint failed: index 'totals_e'; correct the row, or the statement that writes it
---
@ +11:2...41
error: UNIQUE constraint failed: slots.day; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def keyTerms : Database := db! r#"
  CREATE TABLE pairs (x, y);
  INSERT INTO pairs VALUES (1, 1), (1, 1);
  CREATE UNIQUE INDEX pairs_yx ON pairs (y, x);
  CREATE UNIQUE INDEX pairs_e ON pairs (x + 0);
  CREATE TABLE totals (x, y);
  CREATE UNIQUE INDEX totals_e ON totals (x, y * 2);
  INSERT INTO totals VALUES (1, 1), (1, 1);
  CREATE TABLE slots (day, open);
  CREATE UNIQUE INDEX slots_day ON slots (day) WHERE open > 0;
  INSERT INTO slots VALUES (1, 1), (1, 1);"#

-- CHECK: the first in written order, by its text as written or by its name; a name holds for
-- the later constraints of its column.
/--
@ +3:2...34
error: CHECK constraint failed: low > 0; correct the row, or the statement that writes it
---
@ +4:2...34
error: CHECK constraint failed: low + high > 10; correct the row, or the statement that writes it
---
@ +6:2...31
error: CHECK constraint failed: positive; correct the row, or the statement that writes it
---
@ +8:2...31
error: CHECK constraint failed: q; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def checkLabels : Database := db! r#"
  CREATE TABLE ranges (low CHECK (low > 0), high CHECK (high > 0), CHECK (low + high > 10));
  INSERT INTO ranges VALUES (0, 0);
  INSERT INTO ranges VALUES (5, 5);
  CREATE TABLE levels (n CONSTRAINT positive CHECK (n > 0) CHECK (n > 1));
  INSERT INTO levels VALUES (1);
  CREATE TABLE quoted (q CHECK ("q" > 0));
  INSERT INTO quoted VALUES (0);"#

-- STRICT: the storage class of the value, with INT for an integer, and the type of the column.
/--
@ +3:2...43
error: cannot store TEXT value in INT column readings.count; correct the row, or the statement that writes it
---
@ +4:2...39
error: cannot store INT value in BLOB column readings.raw; correct the row, or the statement that writes it
---
@ +5:2...43
error: cannot store TEXT value in REAL column readings.level; correct the row, or the statement that writes it
---
@ +6:2...44
error: cannot store BLOB value in TEXT column readings.note; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def strictTypes : Database := db! r#"
  CREATE TABLE readings (count INT, note TEXT, level REAL, raw BLOB) STRICT;
  INSERT INTO readings (count) VALUES ('x');
  INSERT INTO readings (raw) VALUES (1);
  INSERT INTO readings (level) VALUES ('x');
  INSERT INTO readings (note) VALUES (x'00');"#

-- The checks of one row: NOT NULL before CHECK and before STRICT. The rows of VALUES are checked
-- one at a time: the CHECK failure of the first row comes before the NOT NULL failure of the second.
/--
@ +3:2...37
error: NOT NULL constraint failed: orders.item; correct the row, or the statement that writes it
---
@ +5:2...39
error: NOT NULL constraint failed: gauges.b; correct the row, or the statement that writes it
---
@ +7:2...44
error: CHECK constraint failed: b > 0; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def checkOrder : Database := db! r#"
  CREATE TABLE orders (qty CHECK (qty > 0), item NOT NULL);
  INSERT INTO orders VALUES (0, NULL);
  CREATE TABLE gauges (a INT CHECK (typeof(a) = 'integer'), b TEXT NOT NULL) STRICT;
  INSERT INTO gauges VALUES ('x', NULL);
  CREATE TABLE marks (a NOT NULL, b CHECK (b > 0));
  INSERT INTO marks VALUES (1, 0), (NULL, 5);"#
