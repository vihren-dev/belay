import ViewsSupport

set_option doc.verso true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000

/-! {lit}`PRAGMA table_info` of a view is checked through SQL: the rows come from the resolved
query, and a view that SQLite cannot read gives the preparation error of that query.
Native comparisons check the error messages. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open ViewExamples

namespace ViewTableInfoExamples

/-- A table, a renamed view and a nested view over a failing source. -/
def database : Database := db! r"
  CREATE TABLE t(a INTEGER PRIMARY KEY, b VARCHAR(4) NOT NULL DEFAULT 'x');
  CREATE VIEW v(x, y) AS SELECT a, b FROM t;
  CREATE VIEW broken AS SELECT * FROM missing;
  CREATE VIEW cycle AS SELECT * FROM cycle;
  CREATE VIEW narrow(a, b) AS SELECT 1;
  CREATE VIEW wide(a) AS SELECT * FROM t;
  CREATE VIEW twin(z, z) AS SELECT a, b FROM t;
  CREATE VIEW badnarrow(a, b) AS SELECT * FROM missing;
  CREATE VIEW nested AS SELECT * FROM broken;"

/-- The rows use the explicit column names and the declared types of the source, with
notnull 0, no default and pk 0, although the table has a key, NOT NULL and a default. -/
theorem rows_follow_the_view : (database.run (sql r"PRAGMA table_info(v)")).outputs =
    [.rows [[.integer 0, .text "x".toUTF8.toList, .text "INTEGER".toUTF8.toList, .integer 0, .null, .integer 0],
            [.integer 1, .text "y".toUTF8.toList, .text "VARCHAR(4)".toUTF8.toList, .integer 0, .null, .integer 0]]] := by
  decide +kernel

/-- The pragma reads the view as the current catalog defines it. -/
theorem current_catalog : (database.run (sql r"
    DROP VIEW v; CREATE VIEW v AS SELECT b FROM t; PRAGMA table_info(V);
  ")).outputs = [.done 0, .done 0,
    .rows [[.integer 0, .text "b".toUTF8.toList, .text "VARCHAR(4)".toUTF8.toList, .integer 0, .null, .integer 0]]] := by
  decide +kernel

/-- A name list of another width keeps the list names and drops the declared types, as native
SQLite does; an equal width keeps the types and numbers duplicate names. -/
theorem width_mismatch : (database.run (sql r"PRAGMA table_info(narrow); PRAGMA table_info(twin);")).outputs =
    [.rows [[.integer 0, .text "a".toUTF8.toList, .text [], .integer 0, .null, .integer 0],
            [.integer 1, .text "b".toUTF8.toList, .text [], .integer 0, .null, .integer 0]],
     .rows [[.integer 0, .text "z".toUTF8.toList, .text "INTEGER".toUTF8.toList, .integer 0, .null, .integer 0],
            [.integer 1, .text "z:1".toUTF8.toList, .text "VARCHAR(4)".toUTF8.toList, .integer 0, .null, .integer 0]]] := by
  decide +kernel

/-- A view that cannot be read fails when the pragma is prepared, and the next statement runs. -/
theorem broken_view_fails : (database.run (sql r"PRAGMA table_info(broken); SELECT 1;")).outputs =
    [.error 1, .rows [[.integer 1]]] := by decide +kernel

/-- Model preparation messages are compared with native SQLite in the Python fixture. -/
def messages : List (Option String) := [
  prepareMessage (sql r"PRAGMA table_info(v)") database,
  prepareMessage (sql r"PRAGMA table_info(broken)") database,
  prepareMessage (sql r"PRAGMA table_info(cycle)") database,
  prepareMessage (sql r"PRAGMA table_info(narrow)") database,
  prepareMessage (sql r"PRAGMA table_info(wide)") database,
  prepareMessage (sql r"PRAGMA table_info(twin)") database,
  prepareMessage (sql r"PRAGMA table_info(badnarrow)") database,
  prepareMessage (sql r"PRAGMA table_info(nested)") database,
  prepareMessage (sql r"PRAGMA table_info(missing)") database]

#eval IO.println ("table-info-messages:" ++ (Lean.toJson messages).compress)
#print axioms rows_follow_the_view
#print axioms current_catalog
#print axioms width_mismatch
#print axioms broken_view_fails

end ViewTableInfoExamples
