import Belay

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! The schema, the migrations and the read of the guide's table rebuild (ADR 0017, S6, part 3). The guide makes
{lit}`customers.name` NOT NULL by a rebuild and claims that the rows of {lit}`sessions` survive. This module holds
what the three claims share: a database with the guide's schema, the rebuild in the order that SQLite prescribes
({lit}`requireName`), the same rebuild with the pragma inside the transaction
({lit}`requireNameWrong`) and the read {lit}`allSessions`. The package holds only
general laws; the tables and the statements are part of this fixture. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- A database with the guide's schema and a customer with one session. -/
def sample : Database := db! r"
  CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions(id INTEGER PRIMARY KEY, customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);
  INSERT INTO customers VALUES(1,'ada','Ada@X');
  INSERT INTO sessions VALUES(10,1,100);"

/-- The rebuild of the guide: foreign keys off before the transaction, checked before the commit and on again
after it. -/
def requireName : Script := sql r"
  PRAGMA foreign_keys = OFF;
  BEGIN;
  CREATE TABLE customers_new (id INTEGER PRIMARY KEY, name TEXT NOT NULL, email TEXT NOT NULL);
  INSERT INTO customers_new SELECT id, name, email FROM customers;
  DROP TABLE customers;
  ALTER TABLE customers_new RENAME TO customers;
  PRAGMA foreign_key_check;
  COMMIT;
  PRAGMA foreign_keys = ON;"

/-- The same rebuild with the pragma inside the transaction, where SQLite ignores it. -/
def requireNameWrong : Script := sql r"
  BEGIN;
  PRAGMA foreign_keys = OFF;
  CREATE TABLE customers_new (id INTEGER PRIMARY KEY, name TEXT NOT NULL, email TEXT NOT NULL);
  INSERT INTO customers_new SELECT id, name, email FROM customers;
  DROP TABLE customers;
  ALTER TABLE customers_new RENAME TO customers;
  COMMIT;"

/-- The wrong rebuild on a connection that enforces foreign keys: the first statement turns the enforcement on, as
an application that uses foreign keys does. -/
def requireNameWrongEnforced : Script := sql r"
  PRAGMA foreign_keys = ON;
  BEGIN;
  PRAGMA foreign_keys = OFF;
  CREATE TABLE customers_new (id INTEGER PRIMARY KEY, name TEXT NOT NULL, email TEXT NOT NULL);
  INSERT INTO customers_new SELECT id, name, email FROM customers;
  DROP TABLE customers;
  ALTER TABLE customers_new RENAME TO customers;
  COMMIT;"

/-- The read of the guide: every session. -/
def allSessions : Script := sql r"SELECT id, customer_id, expires_at FROM sessions"

end RebuildGuide
