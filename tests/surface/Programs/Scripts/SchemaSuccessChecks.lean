import RebuildGuide
import Belay.Sqlite.Programs.Claims.SchemaSuccess

open Belay.Sqlite RebuildGuide
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! The schema-only law certifies a transaction and a foreign-key check with a
single possible source of violations. The other checks exercise the conditions
on the transaction state, enforcement and number of result-producing tables. -/

/-- A complete transaction whose successful steps depend only on the schema. -/
private def transaction : Script := sql "BEGIN; CREATE TABLE flags(id INTEGER); DROP TABLE flags; COMMIT;"
example : Succeeds transaction (·.HasCatalog sample) := Script.succeeds_of_schema (by decide +kernel)
example : (sql "BEGIN; BEGIN;").succeedsBySchema sample = false := by decide +kernel
example : (sql "COMMIT;").succeedsBySchema sample = false := by decide +kernel
example : (sql "PRAGMA foreign_keys=ON; BEGIN; COMMIT;").succeedsBySchema sample = false := by decide +kernel
example : (sql "PRAGMA foreign_key_check;").succeedsBySchema sample = true := by decide +kernel

/-- Creating the view, trigger and ordinary index succeeds for every database of the sample schema. -/
private def createObjects : Script := sql r"
  CREATE VIEW customer_ids AS SELECT id FROM customers;
  CREATE TRIGGER observe AFTER INSERT ON customers BEGIN SELECT 1; END;
  CREATE INDEX customer_names ON customers(name);"
example : Succeeds createObjects (·.HasCatalog sample) := Script.succeeds_of_schema (by decide +kernel)

-- Removing an unreferenced column needs only the catalog.
example : (sql "CREATE TABLE flags(id INTEGER, label TEXT); ALTER TABLE flags DROP COLUMN label;").succeedsBySchema sample =
    true := by decide +kernel

-- Existing customers can share a name. A unique index requires a proof about their rows.
example : (sql "CREATE UNIQUE INDEX customer_names ON customers(name);").succeedsBySchema sample = false := by
  decide +kernel

/-- Two child tables can each contribute a nonempty result block in a database of this schema. -/
private def twoChildren : Database := db! r"
CREATE TABLE parent(id INTEGER PRIMARY KEY);
CREATE TABLE a(pid INTEGER REFERENCES parent(id));
CREATE TABLE b(pid INTEGER REFERENCES parent(id));"

example : (sql "PRAGMA foreign_key_check;").succeedsBySchema twoChildren = false := by decide +kernel
example : (sql "PRAGMA foreign_key_check(a);").succeedsBySchema twoChildren = true := by decide +kernel
