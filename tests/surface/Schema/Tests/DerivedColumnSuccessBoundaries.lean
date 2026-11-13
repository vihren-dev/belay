import Belay

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_derived_column_test.py`: the success law of the derived-column
migration from the computed check {lit}`DerivedColumnMigration.succeedsCheck`. The check proves the success
of a migration on two schemas, one of which migrates the second table of its catalog. It is false for a new
typed column of a {lit}`STRICT` table and for a value with a fallible call, and {lit}`#sql_check` shows
that the {lit}`STRICT` migration really fails. -/

namespace DerivedColumnSuccessBoundaries
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open Belay.Sqlite.DerivedColumnMigration

/-- A schema with customers, as the run of its script. -/
def shop : Database := (Database.empty.run (sql r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);")).db

/-- The migration that adds the lower-case email. -/
def addEmailLower : Script := sql r"
  ALTER TABLE customers ADD COLUMN email_lower TEXT;
  UPDATE customers SET email_lower = lower(email);"

/-- On every database with the catalog of {name}`shop` and in every complete environment, the migration
runs without an error. -/
theorem add_email_lower_succeeds : Succeeds addEmailLower (·.HasCatalog shop) :=
  succeeds_of_check (by decide +kernel)

#print axioms add_email_lower_succeeds

/-- A ledger: the migrated table {lit}`entries` is the second table of the catalog. -/
def ledger : Database := (Database.empty.run (sql r"
  CREATE TABLE accounts (id INTEGER PRIMARY KEY, owner TEXT);
  CREATE TABLE entries (id INTEGER PRIMARY KEY, account INTEGER, cents INTEGER NOT NULL, memo TEXT);")).db

/-- The migration: add the column {lit}`dollars` to {lit}`entries` and fill it from {lit}`cents`. -/
def addDollars : Script := sql r"
  ALTER TABLE entries ADD COLUMN dollars REAL;
  UPDATE entries SET dollars = cents / 100.0;"

/-- On every database with the catalog of {name}`ledger`, the migration runs without an error. -/
theorem add_dollars_succeeds : Succeeds addDollars (·.HasCatalog ledger) :=
  succeeds_of_check (by decide +kernel)

#print axioms add_dollars_succeeds

/-- The schema of {name}`shop` as a {lit}`STRICT` table. -/
def strictShop : Database := (Database.empty.run (sql r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL) STRICT;")).db

/-- A migration that writes the text of the email into a new INTEGER column of a {lit}`STRICT` table. -/
def addEmailNumber : Script := sql r"
  ALTER TABLE customers ADD COLUMN n INTEGER;
  UPDATE customers SET n = email;"

example : succeedsCheck strictShop addEmailNumber = false := by decide +kernel
example : succeedsCheck shop (sql r"
  ALTER TABLE customers ADD COLUMN tag TEXT;
  UPDATE customers SET tag = json_extract(name, '$.tag');") = false := by decide +kernel

#sql_check Succeeds addEmailNumber (·.HasCatalog strictShop) with (schema := strictShop)

end DerivedColumnSuccessBoundaries
