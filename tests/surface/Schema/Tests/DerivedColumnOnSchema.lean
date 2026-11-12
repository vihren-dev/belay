import Belay

set_option doc.verso true

/-! The example of the page for agents ({lit}`docs/guide/agents.md`): a migration that adds the column
{lit}`email_lower` to {lit}`customers` and fills it with {lit}`lower(email)`, with claims about every
database of the schema {lit}`shop`. The schema and the migration are SQL files, as in a project. The read
with {lit}`SELECT *` changes ({lit}`star_read_changes`). The read with named columns and the lookup by email
keep their results, and the migration succeeds; each of these proofs is one call of a law of the library
with a check that the kernel evaluates ({lit}`DerivedColumnMigration.preserves_of_check`,
{lit}`DerivedColumnMigration.preserves_of_check_forall` and {lit}`DerivedColumnMigration.succeeds_of_check`). -/

namespace DerivedColumnOnSchema
open Belay.Sqlite

/-- The schema: the database that the statements of {lit}`db/schema.sql` build. -/
def shop : Database := (Database.empty.run (sql_file "db/schema.sql")).db

/-- The migration of {lit}`db/migrations/0003_email_lower.sql`. -/
def addEmailLower : Script := sql_file "db/migrations/0003_email_lower.sql"

/-- The read of all customers with {lit}`SELECT *`. -/
def allCustomers : Script := sql r"SELECT * FROM customers"

/-- The read of all customers with named columns. -/
def namedCustomers : Script := sql r"SELECT id, name, email FROM customers"

/-- The lookup of a customer id by email, with the email as its parameter. -/
def customerIdByEmail (email : Value) : Script :=
  sql r"SELECT id FROM customers WHERE email = ?1" email

/-- The database of the counterexample of {lit}`#sql_check`: one customer with an empty email. -/
def found : Database := db! r"
CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
CREATE TABLE sessions (id INTEGER PRIMARY KEY,
  customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
  expires_at INTEGER NOT NULL);
INSERT INTO customers VALUES (1, NULL, '');"

/-- The migration changes the result of {lit}`SELECT * FROM customers`: each row gets one cell more. -/
theorem star_read_changes :
    ¬ (addEmailLower preserves allCustomers on shop) := by
  sql_refute (db := found)

/-- On every database with the catalog of {lit}`shop` where the migration succeeds, the read of all
customers with named columns gives the same result after the migration as before it. -/
theorem named_read_preserved :
    addEmailLower preserves namedCustomers on shop :=
  DerivedColumnMigration.preserves_of_check (by decide +kernel)

/-- For every email, on every database with the catalog of {lit}`shop` where the migration succeeds, the
lookup of a customer id by email gives the same result after the migration as before it. -/
theorem lookup_read_preserved : ∀ email : Value,
    addEmailLower preserves (customerIdByEmail email) on shop :=
  DerivedColumnMigration.preserves_of_check_forall customerIdByEmail .null (fun _ => rfl) (by decide +kernel)

/-- On every database with the catalog of {lit}`shop` and in every complete environment, the migration runs
without an error. -/
theorem email_lower_succeeds :
    Succeeds addEmailLower (·.HasCatalog shop) :=
  DerivedColumnMigration.succeeds_of_check (by decide +kernel)

#print axioms star_read_changes
#print axioms named_read_preserved
#print axioms lookup_read_preserved
#print axioms email_lower_succeeds

end DerivedColumnOnSchema
