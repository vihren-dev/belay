-- Claims/EmailLower.lean: the claims of db/migrations/0003_email_lower.sql
import Claims.Schema
open Belay.Sqlite

/-- The migration, read from its SQL file, so that the claims are about the SQL that the project runs. -/
def addEmailLower : Script := sql_file "db/migrations/0003_email_lower.sql"

/-- A read of the application. State one claim for each read. -/
def namedCustomers : Script := sql r"SELECT id, name, email FROM customers"

/-- A read with a parameter. -/
def customerByEmail (email : Value) : Script :=
  sql r"SELECT id, name FROM customers WHERE email = ?1" email

-- While you work: check each claim. Write the claim itself after `#sql_check`.
#sql_check Migration.QueryPreserves (send addEmailLower) namedCustomers (·.HasCatalog shop)
#sql_check ∀ email : Value,
  Migration.QueryPreserves (send addEmailLower) (customerByEmail email) (·.HasCatalog shop)
#sql_check Succeeds addEmailLower (·.HasCatalog shop)

-- When an answer is `false`: keep its database, with the statements that the answer
-- prints after `Construction:`, and prove the fact.
--
-- def found : Database := db! r"
--   CREATE TABLE …;
--   INSERT INTO … VALUES (…);"
--
-- theorem old_read_changes :
--     ¬ Migration.QueryPreserves (send addEmailLower) oldRead (·.HasCatalog shop) := by
--   sql_refute (db := found)
--
-- theorem new_read_kept_on_found :
--     (found.run newRead).outputs = ((found.run addEmailLower).db.run newRead).outputs := by
--   decide +kernel

-- Before you finish: replace each `#sql_check` with its theorem, or with a comment
-- that gives the claim and its answer. End the file with one line for each theorem:
--
-- #print axioms old_read_changes
