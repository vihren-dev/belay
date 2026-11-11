import Belay

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! Actual runs of the table rebuild of the guide and of DROP COLUMN (ADR 0019, D4, part 3). The parent table
{lit}`p` has the rows (1, 'x', 10) and (2, 'y', 20), and the child {lit}`c` has three rows that refer to it with
{lit}`ON DELETE CASCADE`. The rebuild creates {lit}`p_new` without the third column, copies the rows, drops {lit}`p` and
renames {lit}`p_new` to {lit}`p`. Each run is also a native comparison ({lit}`conformance/authored_rebuilds.py`): the
rows, the outputs and the two foreign-key atoms agree with SQLite 3.51.0. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace RebuildRunsFixture

/-- Both foreign-key atoms of a database under the mapping that its own catalog selects. -/
abbrev Atoms (database : Model.Database) : Prop :=
  database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
    database.RowReferencesHold database.catalog.foreignKeyMapping

/-- The parent and the child of the rebuild. -/
def family : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(id INTEGER PRIMARY KEY, name TEXT, extra INTEGER);
  INSERT INTO p VALUES(1,'x',10),(2,'y',20);
  CREATE TABLE c(id INTEGER PRIMARY KEY, pid INTEGER REFERENCES p(id) ON DELETE CASCADE, note TEXT);
  INSERT INTO c VALUES(10,1,'a'),(11,2,'b'),(12,2,'c');"

/-- The rows of the child, as pairs of the rowid and the cells. -/
def childRows (database : Model.Database) : List (Int × List Value) :=
  (database.rowsAt 0).map fun row => (row.rowid, row.values)

/-- The corrected rebuild keeps the three rows of the child and the two rows of the parent without the dropped column,
and both foreign-key atoms hold. -/
theorem corrected_rebuild_keeps_rows : let result := family.raw.run (sql r"BEGIN;
      CREATE TABLE p_new(id INTEGER PRIMARY KEY, name TEXT); INSERT INTO p_new SELECT id, name FROM p;
      DROP TABLE p; ALTER TABLE p_new RENAME TO p; COMMIT;")
    childRows result.connection.state.database =
      [(10, [.integer 10, .integer 1, .text [97]]), (11, [.integer 11, .integer 2, .text [98]]),
        (12, [.integer 12, .integer 2, .text [99]])] ∧
    (result.connection.state.database.rowsAt 1).map (·.values) =
      [[.integer 1, .text [120]], [.integer 2, .text [121]]] ∧
    Atoms result.connection.state.database := by decide +kernel

/-- The unsafe rebuild with enforcement on: the DROP TABLE removes the rows of {lit}`p` one by one, and the cascade
deletes the rows of the child. The new table has its rows, the child has none, and both atoms hold. -/
theorem unsafe_rebuild_cascades : let result := family.raw.run (sql r"PRAGMA foreign_keys = ON; BEGIN;
      CREATE TABLE p_new(id INTEGER PRIMARY KEY, name TEXT); INSERT INTO p_new SELECT id, name FROM p;
      DROP TABLE p; ALTER TABLE p_new RENAME TO p; COMMIT;")
    childRows result.connection.state.database = [] ∧
    (result.connection.state.database.rowsAt 1).map (·.values) =
      [[.integer 1, .text [120]], [.integer 2, .text [121]]] ∧
    Atoms result.connection.state.database := by decide +kernel

/-- A pragma inside a transaction does nothing: with enforcement on before the transaction, turning it off after
{lit}`BEGIN` leaves it on, so the cascade still happens. -/
theorem pragma_in_transaction_does_nothing : let result := family.raw.run (sql r"PRAGMA foreign_keys = ON; BEGIN;
      PRAGMA foreign_keys = OFF; DROP TABLE p; COMMIT;")
    childRows result.connection.state.database = [] := by decide +kernel

/-- A rebuild that leaves a parent row out, with enforcement off: the children of the missing row stay, so the row
atom fails, which is what {lit}`PRAGMA foreign_key_check` reports, and the parent schemas stay compatible. -/
theorem corrected_rebuild_with_a_missing_parent : let result := family.raw.run (sql r"BEGIN;
      CREATE TABLE p_new(id INTEGER PRIMARY KEY, name TEXT); INSERT INTO p_new SELECT id, name FROM p WHERE id = 1;
      DROP TABLE p; ALTER TABLE p_new RENAME TO p; COMMIT;")
    (childRows result.connection.state.database).length = 3 ∧
    ¬ result.connection.state.database.RowReferencesHold result.connection.state.database.catalog.foreignKeyMapping ∧
    result.connection.state.database.ParentSchemasCompatible result.connection.state.database.catalog.foreignKeyMapping := by
  decide +kernel

/-- A rollback of the whole rebuild restores the tables with all their columns and rows. -/
theorem rollback_restores_the_tables : let result := family.raw.run (sql r"PRAGMA foreign_keys = ON; BEGIN;
      CREATE TABLE p_new(id INTEGER PRIMARY KEY, name TEXT); INSERT INTO p_new SELECT id, name FROM p;
      DROP TABLE p; ALTER TABLE p_new RENAME TO p; ROLLBACK;")
    result.connection.state.database = family.raw := by
  decide +kernel

/-- A table with an index and two rows, for DROP COLUMN. -/
def simple : Belay.Sqlite.Database := db! r"
  CREATE TABLE t(a INTEGER PRIMARY KEY, b TEXT, c INTEGER, d INTEGER); CREATE INDEX ti ON t(c);
  INSERT INTO t VALUES(1,'p',15,10),(5,NULL,25,20);"

/-- DROP COLUMN of the second column removes its cell from each row and keeps the rowids, the order and the other cells. -/
theorem drop_column_keeps_the_other_cells : let result := simple.raw.run (sql r"ALTER TABLE t DROP COLUMN b;")
    (result.connection.state.database.rowsAt 0).map (fun row => (row.rowid, row.values)) =
      [(1, [.integer 1, .integer 15, .integer 10]), (5, [.integer 5, .integer 25, .integer 20])] := by
  decide +kernel

/-- DROP COLUMN of the primary key column is refused by SQLite and keeps the database. -/
theorem drop_primary_key_keeps_the_database : let result := simple.raw.run (sql r"ALTER TABLE t DROP COLUMN a;")
    result.connection.state.database = simple.raw := by decide +kernel

#print axioms corrected_rebuild_keeps_rows
#print axioms unsafe_rebuild_cascades
#print axioms pragma_in_transaction_does_nothing
#print axioms corrected_rebuild_with_a_missing_parent
#print axioms rollback_restores_the_tables
#print axioms drop_column_keeps_the_other_cells
#print axioms drop_primary_key_keeps_the_database

end RebuildRunsFixture
