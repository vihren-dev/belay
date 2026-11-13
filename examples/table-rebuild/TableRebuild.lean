import Belay
import RebuildKeeps -- the proof of `fixed_keeps_sessions`, in the folder `Proof`

/-! The table rebuild of Belay's README, in the order of the README. A migration makes the table
`customers` STRICT. The check finds a database on which the migration loses the sessions; the fixed
migration keeps them on every database of the schema, and the theorem `fixed_keeps_sessions` says so.
The success of the fixed migration is in `FixedSucceeds.lean`. -/

open Belay.Sqlite

/-- The schema of the example, without rows. -/
def shop : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions (id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);"

/-- The migration with the mistake: `PRAGMA foreign_keys` does nothing inside a transaction, so
`DROP TABLE customers` deletes the sessions of each customer. -/
def badMigration : Script := sql r"
  PRAGMA foreign_keys = ON;
  BEGIN;
  PRAGMA foreign_keys = OFF;
  CREATE TABLE customers_new (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL) STRICT;
  INSERT INTO customers_new SELECT id, name, email FROM customers;
  DROP TABLE customers;
  ALTER TABLE customers_new RENAME TO customers;
  COMMIT;"

/-- The read that a correct migration keeps: every session. -/
def allSessions : Script := sql r"SELECT id, customer_id, expires_at FROM sessions"

-- Answers `false`, with one customer and one session.
#sql_check badMigration preserves allSessions on shop

/-- The counterexample that the check found. -/
def found : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions (id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);
  INSERT INTO customers VALUES (1, NULL, '');
  INSERT INTO sessions VALUES (1, 1, 0);"

/-- On `found`, every statement of `badMigration` succeeds, and the session is gone. -/
example : (found.run badMigration).outputs.allOk = true ∧
    ((found.run badMigration).db.run allSessions).outputs.getLast? = some (.rows []) := by
  decide +kernel

/-- The fixed migration: foreign keys off before the transaction, checked before the commit. -/
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

/-- On `found`, every statement of `fixedMigration` succeeds, and the session stays. -/
example : (found.run fixedMigration).outputs.allOk = true ∧
    ((found.run fixedMigration).db.run allSessions).outputs.getLast? = some (.rows [[1, 1, 0]]) := by
  decide +kernel

/-- The schema `shop` has the catalog of the database that the proof modules use. -/
theorem shop_catalog : shop.raw.catalog = RebuildGuide.sample.raw.catalog := by decide +kernel

/-- For every database with the catalog of `shop` and every complete environment: where
`fixedMigration` succeeds on the database, `allSessions` before it and after it gives the same value
and the same outputs. Where the migration fails, the claim requires nothing. Proof sketch:
`RebuildGuide.makeStrict_preserves_allSessions` in `Proof/RebuildKeeps.lean`; `fixedMigration` has
the statements of `RebuildGuide.makeStrict`, and `shop_catalog` gives its premise. -/
theorem fixed_keeps_sessions :
    fixedMigration preserves allSessions on shop := by
  intro db onShop
  exact RebuildGuide.makeStrict_preserves_allSessions db (onShop.trans shop_catalog)

#print axioms fixed_keeps_sessions
