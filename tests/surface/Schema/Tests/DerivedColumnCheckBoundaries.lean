import Belay

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_derived_column_test.py`: the boundaries of the computed check
{lit}`DerivedColumnMigration.preservesCheck`. The kernel evaluates the check to false for each case that the
check does not cover: a read with {lit}`SELECT *`, a new column with a name that the table has, a written value
that reads a parameter or the clock, a new column with a constraint, and a trigger that an UPDATE of the
table fires. The checks also hold on a schema that {lit}`db!` gives. A second schema, whose migrated table is the second table of its catalog and whose read filters
an INTEGER column by a bound value, gives a theorem for every bound value
({lit}`big_entries_preserved`). -/

namespace DerivedColumnCheckBoundaries
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open Belay.Sqlite.DerivedColumnMigration

/-- The schema of the false cases, as the run of its script. -/
def shop : Database := (Database.empty.run (sql r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);")).db

/-- The schema of {name}`shop` with a log table and a trigger that every UPDATE of {lit}`customers` fires. -/
def shopWithTrigger : Database := (Database.empty.run (sql r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE log (x TEXT);
  CREATE TRIGGER logged AFTER UPDATE ON customers BEGIN INSERT INTO log VALUES (new.name); END;")).db

/-- Whether the check holds for the migration and the statements of the read, on the schema. -/
def checked (schema : Database) (migration read : Script) : Bool :=
  preservesCheck schema migration (read.statements.map Prod.fst)

/-- The migration that the check covers on {name}`shop`. -/
def addEmailLower : Script := sql r"
  ALTER TABLE customers ADD COLUMN email_lower TEXT;
  UPDATE customers SET email_lower = lower(email);"

/-- A read with named columns. -/
def namedCustomers : Script := sql r"SELECT id, name, email FROM customers"

/-- A read whose result gets the new column. -/
def allCustomers : Script := sql r"SELECT * FROM customers"

example : checked shop addEmailLower namedCustomers = true := by decide +kernel

/-- The schema of {name}`shop` as a {lit}`db!` database, with one row. -/
def shopWithRow : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  INSERT INTO customers VALUES (1, 'Ann', 'ann@x.io');"

example : checked shopWithRow addEmailLower namedCustomers = true := by decide +kernel
example : succeedsCheck shopWithRow addEmailLower = true := by decide +kernel
example : checked shop addEmailLower allCustomers = false := by decide +kernel
example : checked shop (sql r"
  ALTER TABLE customers ADD COLUMN email TEXT;
  UPDATE customers SET email = lower(email);") namedCustomers = false := by decide +kernel
example : checked shop (sql r"
  ALTER TABLE customers ADD COLUMN email_lower TEXT;
  UPDATE customers SET email_lower = ?1;" (Value.integer 1)) namedCustomers = false := by decide +kernel
example : checked shop (sql r"
  ALTER TABLE customers ADD COLUMN seen TEXT;
  UPDATE customers SET seen = datetime('now');") namedCustomers = false := by decide +kernel
example : checked shop (sql r"
  ALTER TABLE customers ADD COLUMN email_lower TEXT NOT NULL DEFAULT '';
  UPDATE customers SET email_lower = lower(email);") namedCustomers = false := by decide +kernel
example : checked shopWithTrigger addEmailLower namedCustomers = false := by decide +kernel

/-- A ledger: the migrated table {lit}`entries` is the second table of the catalog. -/
def ledger : Database := (Database.empty.run (sql r"
  CREATE TABLE accounts (id INTEGER PRIMARY KEY, owner TEXT);
  CREATE TABLE entries (id INTEGER PRIMARY KEY, account INTEGER, cents INTEGER NOT NULL, memo TEXT);")).db

/-- The migration: add the column {lit}`dollars` to {lit}`entries` and fill it from {lit}`cents`. -/
def addDollars : Script := sql r"
  ALTER TABLE entries ADD COLUMN dollars REAL;
  UPDATE entries SET dollars = cents / 100.0;"

/-- The entries above a limit in cents. -/
def bigEntries (limit : Value) : Script := sql r"SELECT id, memo FROM entries WHERE cents > ?1" limit

/-- For every limit, on every database with the catalog of {name}`ledger` where the migration succeeds, the
read of the entries above the limit gives the same result after the migration as before it. -/
theorem big_entries_preserved : ∀ limit : Value, addDollars preserves (bigEntries limit) on ledger :=
  preserves_of_check_forall bigEntries .null (fun _ => rfl) (by decide +kernel)

#print axioms big_entries_preserved

end DerivedColumnCheckBoundaries
