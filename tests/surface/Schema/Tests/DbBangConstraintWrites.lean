import Belay

/-! A fixture of `tests/surface_guide_test.py`: `db! r"..."` names the constraint that an INSERT
with ON CONFLICT or an algorithm, or an UPDATE, fails as SQLite 3.51 does, gives SQLite's text
for a CHECK of ADD COLUMN, and says that it does not name the constraint of a write that runs a
trigger or that checks foreign keys (`constraintMessage` of `Model/ExecutionMessages.lean`, from
`failingConstraints` of `Model/FailingConstraints.lean`, at the statement by
`Belay/Sqlite/DbDiagnostics.lean`). Each expected message has SQLite's text as the native
`sqlite3` shell 3.51 gives it for the same SQL; where SQLite's choice may depend on what the model
does not keep, the message names each candidate, and a comment gives SQLite's text.
`#guard_msgs (positions := true)` checks each message and its position as `@ +line:start...stop`,
with the line from the command and columns from 0. The file fails to elaborate when a message or a
position is not the expected one. -/

open Belay.Sqlite

-- INSERT with ON CONFLICT: DO UPDATE that breaks NOT NULL, CHECK and UNIQUE, DO NOTHING with
-- a NULL in a NOT NULL column, and OR FAIL at its second row.
/--
@ +4:2...79
error: NOT NULL constraint failed: stock.qty; correct the row, or the statement that writes it
---
@ +5:2...78
error: CHECK constraint failed: price > 0; correct the row, or the statement that writes it
---
@ +6:2...76
error: UNIQUE constraint failed: stock.sku; correct the row, or the statement that writes it
---
@ +7:2...62
error: NOT NULL constraint failed: stock.qty; correct the row, or the statement that writes it
---
@ +8:2...58
error: NOT NULL constraint failed: stock.qty; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def upserts : Database := db! r#"
  CREATE TABLE stock (sku UNIQUE, qty NOT NULL, price CHECK (price > 0));
  INSERT INTO stock VALUES (1, 1, 1), (2, 2, 2);
  INSERT INTO stock VALUES (1, 1, 1) ON CONFLICT (sku) DO UPDATE SET qty = NULL;
  INSERT INTO stock VALUES (1, 1, 1) ON CONFLICT (sku) DO UPDATE SET price = 0;
  INSERT INTO stock VALUES (1, 1, 1) ON CONFLICT (sku) DO UPDATE SET sku = 2;
  INSERT INTO stock VALUES (3, NULL, 1) ON CONFLICT DO NOTHING;
  INSERT OR FAIL INTO stock VALUES (3, 3, 3), (1, NULL, 1);"#

-- UPDATE of one row gives SQLite's message. UPDATE of several rows names the first failure of
-- each row, because SQLite's query planner chooses the order of the rows. SQLite 3.51 gives
-- `CHECK constraint failed: first_positive` and `UNIQUE constraint failed: cards.back`. The
-- last UPDATE assigns a column that the filter of a partial unique index reads.
/--
@ +6:2...42
error: CHECK constraint failed: third_positive; correct the row, or the statement that writes it
---
@ +7:2...29
error: a constraint failed, and SQLite names one of these: "CHECK constraint failed: first_positive" or "CHECK constraint failed: third_positive". Which one may depend on the order in which the UPDATE visits the rows, which the model does not keep; correct the row, or the statement that writes it
---
@ +10:2...38
error: a constraint failed, and SQLite names one of these: "UNIQUE constraint failed: cards.front" or "UNIQUE constraint failed: cards.back". Which one may depend on the order in which the UPDATE visits the rows, which the model does not keep; correct the row, or the statement that writes it
---
@ +14:2...28
error: UNIQUE constraint failed: shifts.day; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def updates : Database := db! r#"
  CREATE TABLE steps (id INTEGER PRIMARY KEY, weight,
    CONSTRAINT first_positive CHECK (id <> 1 OR weight > 0),
    CONSTRAINT third_positive CHECK (id <> 3 OR weight > 0));
  INSERT INTO steps VALUES (1, 30), (2, 20), (3, 10);
  UPDATE steps SET weight = 0 WHERE id = 3;
  UPDATE steps SET weight = 0;
  CREATE TABLE cards (front UNIQUE, back UNIQUE);
  INSERT INTO cards VALUES (1, 1), (2, 2);
  UPDATE cards SET front = 3, back = 3;
  CREATE TABLE shifts (day, open);
  CREATE UNIQUE INDEX shifts_day ON shifts (day) WHERE open > 0;
  INSERT INTO shifts VALUES (1, 0), (1, 1);
  UPDATE shifts SET open = 1;"#

-- UPDATE of several rows where a row conflicts with another row in its old values only: a key
-- with an expression term, and a partial unique index whose filter reads an assigned column.
-- The final table conflicts on another key. SQLite 3.51 gives
-- `UNIQUE constraint failed: index 'sums_total'`, `UNIQUE constraint failed: flags.a` and
-- `UNIQUE constraint failed: index 'pairs2_sum'`.
/--
@ +6:2...30
error: a constraint failed, and SQLite names one of these: "UNIQUE constraint failed: sums.c" or "UNIQUE constraint failed: index 'sums_total'". Which one may depend on the order in which the UPDATE visits the rows, which the model does not keep; correct the row, or the statement that writes it
---
@ +11:2...31
error: a constraint failed, and SQLite names one of these: "UNIQUE constraint failed: flags.d" or "UNIQUE constraint failed: flags.a". Which one may depend on the order in which the UPDATE visits the rows, which the model does not keep; correct the row, or the statement that writes it
---
@ +15:2...25
error: a constraint failed, and SQLite names one of these: "UNIQUE constraint failed: pairs2.a" or "UNIQUE constraint failed: index 'pairs2_sum'". Which one may depend on the order in which the UPDATE visits the rows, which the model does not keep; correct the row, or the statement that writes it
-/
#guard_msgs (positions := true) in
def oldValueConflicts : Database := db! r#"
  CREATE TABLE sums (a, b, c);
  CREATE UNIQUE INDEX sums_c ON sums (c);
  CREATE UNIQUE INDEX sums_total ON sums (a + b);
  INSERT INTO sums VALUES (3, 9, 1), (1, 2, 2);
  UPDATE sums SET b = 0, c = 5;
  CREATE TABLE flags (a, b, c, d);
  CREATE UNIQUE INDEX flags_d ON flags (d);
  CREATE UNIQUE INDEX flags_a ON flags (a) WHERE b > c;
  INSERT INTO flags VALUES (1, 10, 20, 1), (1, 3, 0, 2);
  UPDATE flags SET c = 5, d = 7;
  CREATE TABLE pairs2 (a UNIQUE, b);
  CREATE UNIQUE INDEX pairs2_sum ON pairs2 (a + b);
  INSERT INTO pairs2 VALUES (0, 1), (2, 4);
  UPDATE pairs2 SET a = 5;"#

-- ADD COLUMN whose default fails its CHECK constraint: SQLite's message has no label, and the
-- error is not a constraint error.
/--
@ +4:2...62
error: CHECK constraint failed; correct the statement, or the statements before it that give the data that it reads
-/
#guard_msgs (positions := true) in
def addColumnDefault : Database := db! r#"
  CREATE TABLE notes (body);
  INSERT INTO notes VALUES ('x');
  ALTER TABLE notes ADD COLUMN rank DEFAULT 0 CHECK (rank > 0);"#

-- A write that can fire a trigger or that checks foreign keys: the model does not name the
-- constraint, also for a trigger whose WHEN is always false. SQLite 3.51 gives
-- `NOT NULL constraint failed: entries.body`, `FOREIGN KEY constraint failed` and
-- `NOT NULL constraint failed: quiet.a`.
/--
@ +5:2...35
error: constraint failed; the model does not name the constraint that fails in a write that can fire a trigger or that checks foreign keys. Run the statement in the sqlite3 shell to see SQLite's message
---
@ +9:2...29
error: constraint failed; the model does not name the constraint that fails in a write that can fire a trigger or that checks foreign keys. Run the statement in the sqlite3 shell to see SQLite's message
---
@ +12:2...33
error: constraint failed; the model does not name the constraint that fails in a write that can fire a trigger or that checks foreign keys. Run the statement in the sqlite3 shell to see SQLite's message
-/
#guard_msgs (positions := true) in
def triggerOrKey : Database := db! r#"
  CREATE TABLE entries (body NOT NULL);
  CREATE TABLE audit (body);
  CREATE TRIGGER entries_audit AFTER INSERT ON entries BEGIN INSERT INTO audit VALUES (new.body); END;
  INSERT INTO entries VALUES (NULL);
  PRAGMA foreign_keys = ON;
  CREATE TABLE owners (id INTEGER PRIMARY KEY);
  CREATE TABLE pets (owner REFERENCES owners (id));
  INSERT INTO pets VALUES (1);
  CREATE TABLE quiet (a NOT NULL);
  CREATE TRIGGER quiet_never AFTER INSERT ON quiet WHEN 0 BEGIN INSERT INTO audit VALUES (new.a); END;
  INSERT INTO quiet VALUES (NULL);"#
