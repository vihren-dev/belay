import Belay

/-! A fixture of `tests/surface_guide_test.py`: `sql! db r"..."` (`Belay/Sqlite/SqlBang.lean`,
`Belay/Sqlite/SqlDiagnostics.lean`) shows each error of the SQL text at its position in the
text. `#guard_msgs (positions := true)` checks each message and its position
as `@ +line:start...stop`, with the line from the command and columns from 0. The file fails to
elaborate when a message or a position is not the expected one. -/

open Belay.Sqlite

/-- The guide's database `shop`: the table `invoices` with two rows. -/
def shop : Database := db! r"
  CREATE TABLE invoices (
    id INTEGER PRIMARY KEY,
    customer TEXT NOT NULL,
    amount INTEGER NOT NULL CHECK (amount >= 0),
    status TEXT NOT NULL DEFAULT 'open'
  );
  INSERT INTO invoices (id, customer, amount) VALUES (1, 'acme', 10), (2, 'zeta', 0);"

-- A misspelled column: SQLite's prepare error, at the name.
/--
@ +1:46...50
error: no such column: nmae
-/
#guard_msgs (positions := true) in
def misspelled : Script := sql! shop r"SELECT nmae FROM invoices"

-- A table that `shop` does not have: SQLite's prepare error, at the name.
/--
@ +1:56...65
error: no such table: customers
-/
#guard_msgs (positions := true) in
def missingTable : Script := sql! shop r"SELECT id FROM customers"

-- A raw string with `#` and a quoted name after a string literal: at the quoted name.
/--
@ +1:52...58
error: no such column: Nmae
-/
#guard_msgs (positions := true) in
def quotedName : Script := sql! shop r#"SELECT '#', [Nmae] FROM invoices"#

-- A model restriction: the model's reason, at the node of its path.
/--
@ +1:54...59
error: the rowid names rowid, _rowid_ and oid are not modeled in expressions over a table, as the SET column of a table without an INTEGER PRIMARY KEY, or in an INSERT column list; name the table's columns
-/
#guard_msgs (positions := true) in
def restricted : Script := sql! shop r"SELECT amount, rowid FROM invoices"

-- A qualified name, at the qualifier and the column; a string literal with the text of a name
-- is not the name.
/--
@ +1:45...58
error: no such column: invoices.nmae
---
@ +1:89...93
error: no such column: nmae
-/
#guard_msgs (positions := true) in
def qualified : Script := sql! shop r"SELECT invoices.nmae FROM invoices; SELECT 'nmae', nmae FROM invoices"

-- Each prepare error and the first restriction; the statements after it show no error.
/--
@ +1:43...47
error: no such column: nmae
---
@ +1:70...75
error: the rowid names rowid, _rowid_ and oid are not modeled in expressions over a table, as the SET column of a table without an INTEGER PRIMARY KEY, or in an INSERT column list; name the table's columns
-/
#guard_msgs (positions := true) in
def several : Script := sql! shop r"SELECT nmae FROM invoices; SELECT rowid FROM invoices; SELECT zz FROM u"

-- SQL that SQLite's grammar rejects, at the offset where it rejects it.
/--
@ +1:52...53
error: SQLite's grammar rejects the SQL at this offset; correct the SQL there and run the command again
-/
#guard_msgs (positions := true) in
def rejected : Script := sql! shop r"SELECT id FORM invoices"

-- A qualified name in WHERE and in JOIN ... ON: at the qualifier, the dot and the column.
/--
@ +1:73...86
error: no such column: invoices.nmae
-/
#guard_msgs (positions := true) in
def qualifiedWhere : Script := sql! shop r"SELECT id FROM invoices WHERE invoices.nmae = 1"

/--
@ +1:90...103
error: no such column: invoices.nmae
-/
#guard_msgs (positions := true) in
def qualifiedJoin : Script := sql! shop r"SELECT j.id FROM invoices AS j JOIN invoices ON invoices.nmae = j.id"

-- A name that the statement writes more than once, here as an alias and as a column, or as a
-- column and as a table: at the statement, because only the role tells which one is meant.
/--
@ +1:39...76
error: no such column: nmae
-/
#guard_msgs (positions := true) in
def twiceAlias : Script := sql! shop r"SELECT id AS nmae, nmae FROM invoices"

/--
@ +1:39...98
error: no such table: u
-/
#guard_msgs (positions := true) in
def twiceTable : Script := sql! shop r"SELECT id FROM invoices WHERE customer IN (SELECT u FROM u)"

-- Text with characters of more than one byte before the name: at the name, in a raw string and
-- in a plain string.
/--
@ +1:49...53
error: no such column: nmae
-/
#guard_msgs (positions := true) in
def wideRaw : Script := sql! shop r"SELECT 'éé', nmae FROM invoices"

/--
@ +1:50...54
error: no such column: nmae
-/
#guard_msgs (positions := true) in
def widePlain : Script := sql! shop "SELECT 'éé', nmae FROM invoices"

-- A plain string with an escape: at the whole literal, because the bytes of the text are then not
-- the bytes of the source (`textRange`).
/--
@ +1:34...62
error: no such column: nmae
-/
#guard_msgs (positions := true) in
def escaped : Script := sql! shop "SELECT nmae\nFROM invoices"
