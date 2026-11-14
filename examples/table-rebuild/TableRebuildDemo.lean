import Belay
import RebuildKeeps -- the proof of `fixed_keeps_sessions`, in the folder `Proof`
open Belay.Sqlite

def shop : Database := db! r"
  CREATE TABLE customers (
    id INTEGER PRIMARY KEY,
    name TEXT,
    email TEXT NOT NULL
  );
  CREATE TABLE sessions (
    id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL
      REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL
  );"

def badMigration : Script := sql r"
  PRAGMA foreign_keys = ON;
  BEGIN;
  PRAGMA foreign_keys = OFF;
  CREATE TABLE customers_new (
    id INTEGER PRIMARY KEY,
    name TEXT,
    email TEXT NOT NULL
  ) STRICT;
  INSERT INTO customers_new SELECT id, name, email FROM customers;
  DROP TABLE customers;
  ALTER TABLE customers_new RENAME TO customers;
  COMMIT;"

def allSessions : Script := sql r"
  SELECT id, customer_id, expires_at FROM sessions"

#sql_check badMigration preserves allSessions on shop

def fixedMigration : Script := sql r"
  -- before the transaction, where it takes effect
  PRAGMA foreign_keys = OFF;
  BEGIN;
  CREATE TABLE customers_new (
    id INTEGER PRIMARY KEY,
    name TEXT,
    email TEXT NOT NULL
  ) STRICT;
  INSERT INTO customers_new SELECT id, name, email FROM customers;
  DROP TABLE customers;
  ALTER TABLE customers_new RENAME TO customers;
  COMMIT;
  -- on again after the commit
  PRAGMA foreign_keys = ON;"

theorem fixed_keeps_sessions :
    fixedMigration preserves allSessions on shop := by
  intro db onShop
  exact RebuildGuide.makeStrict_preserves_allSessions
    db (onShop.trans (by decide +kernel))

#print axioms fixed_keeps_sessions
