import RebuildSucceeds

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! The rebuild example of the README, with its names and its notation: the schema {lit}`shop`, the wrong rebuild
{lit}`badMigration`, the fixed rebuild {lit}`fixedMigration` and the read {lit}`allSessions`. The README shows the
definitions, the check of {lit}`badMigration` and its answer, the facts about the database {lit}`found` and the
theorem {lit}`fixed_keeps_sessions`. The check of success and its theorem show the short form
{lit}`succeeds on shop` on the same example. The theorems reuse the proofs of {lit}`RebuildKeeps` and {lit}`RebuildSucceeds`, which state the same
claims for the rebuild {lit}`makeStrict` with the premise that the catalog is the one of {lit}`sample`. -/

open Belay.Sqlite
namespace RebuildGuide

/-- The schema of the README, without rows. -/
def shop : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions (id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);"

/-- The wrong rebuild of the README: the pragma that turns foreign keys off is inside the transaction, where
SQLite ignores it, so dropping the customers deletes their sessions. -/
def badMigration : Script := sql r"
  PRAGMA foreign_keys = ON;
  BEGIN;
  PRAGMA foreign_keys = OFF;
  CREATE TABLE customers_new (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL) STRICT;
  INSERT INTO customers_new SELECT id, name, email FROM customers;
  DROP TABLE customers;
  ALTER TABLE customers_new RENAME TO customers;
  COMMIT;"

/-- The fixed rebuild of the README, with its comments. -/
def fixedMigration : Script := sql r"
  PRAGMA foreign_keys = OFF;           -- before the transaction, where it takes effect
  BEGIN;
  CREATE TABLE customers_new (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL) STRICT;
  INSERT INTO customers_new SELECT id, name, email FROM customers;
  DROP TABLE customers;
  ALTER TABLE customers_new RENAME TO customers;
  PRAGMA foreign_key_check;            -- fails the migration on a dangling reference
  COMMIT;
  PRAGMA foreign_keys = ON;"           -- on again after the commit

#sql_check badMigration preserves allSessions on shop

#sql_check fixedMigration succeeds on shop

/-- The counterexample of the first check, as the README keeps it. -/
def found : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions (id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);
  INSERT INTO customers VALUES (1, NULL, '');
  INSERT INTO sessions VALUES (1, 1, 0);"

/-- On {name}`found`, every statement of the wrong rebuild succeeds, and the read after it returns no session. -/
example : (found.run badMigration).outputs.allOk = true ∧
    ((found.run badMigration).db.run allSessions).outputs.getLast? = some (.rows []) := by
  decide +kernel

/-- On {name}`found`, every statement of the fixed rebuild succeeds, and the read after it returns the session. -/
example : (found.run fixedMigration).outputs.allOk = true ∧
    ((found.run fixedMigration).db.run allSessions).outputs.getLast? = some (.rows [[1, 1, 0]]) := by
  decide +kernel

/-- The fixed rebuild of the README has the statements of {name}`makeStrict`. -/
theorem fixedMigration_eq : fixedMigration = makeStrict := rfl

/-- The schema of the README has the catalog of {name}`sample`. -/
theorem shop_catalog : shop.raw.catalog = sample.raw.catalog := by decide +kernel

/-- For every database with the catalog of {name}`shop` and every complete environment: where the fixed rebuild
succeeds on the database, the read {name}`allSessions` before it and after it gives the same value and the same
outputs. Where the rebuild fails, the claim requires nothing. Proof sketch: {name}`makeStrict_preserves_allSessions`,
with {name}`fixedMigration_eq` and {name}`shop_catalog`. -/
theorem fixed_keeps_sessions : fixedMigration preserves allSessions on shop := by
  rw [fixedMigration_eq]
  intro db pre
  exact makeStrict_preserves_allSessions db (pre.trans shop_catalog)

/-- For every database with the catalog of {name}`shop` whose customers all fit the STRICT types of the new table
({name}`StrictRows`), and every complete environment: the fixed rebuild runs without an error, on the actual run
and on every branch. Where a customer does not fit, for example with a blob email, the claim requires nothing.
Proof sketch: {name}`makeStrict_succeeds`, with {name}`fixedMigration_eq` and {name}`shop_catalog`. -/
theorem fixed_succeeds : Succeeds fixedMigration (fun db => db.HasCatalog shop ∧ StrictRows db) := by
  rw [fixedMigration_eq]
  intro db ⟨pre, fits⟩
  exact makeStrict_succeeds db ⟨pre.trans shop_catalog, fits⟩

#print axioms fixed_keeps_sessions
#print axioms fixed_succeeds

end RebuildGuide
