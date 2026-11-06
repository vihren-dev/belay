import Belay

open Belay.Sqlite Lean Elab

/-! The claim of issue #318 on the tables that a developer has: an INTEGER PRIMARY KEY, a CHECK on
the email and one supplied row. The search builds variants of the supplied row, and the replay
builds each table from the schema's SQL text. The claim of issue #293 checks an INSERT on a schema
with a primary key. The test is {lit}`tests/surface_check_real_schemas_test.py`. -/

/-- Mark the message of one command, so the test reads each block. -/
elab "labelled_sql " label:str " in " cmd:command : command => do
  logInfo m!"SQL-COMMAND-BEGIN {label.getString}"
  Command.elabCommand cmd
  logInfo m!"SQL-COMMAND-END {label.getString}:"

set_option maxHeartbeats 4000000

def uniqueEmail := sql r"CREATE UNIQUE INDEX unique_email ON customers(email COLLATE NOCASE)"
def noDuplicateEmails : Script := sql r"
  SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM customers GROUP BY email HAVING count(*) > 1)"

/-- One email column without constraints. -/
def onePlain : Database := db! r"
  CREATE TABLE customers (email TEXT NOT NULL);
  INSERT INTO customers VALUES ('ann@x.io');"

/-- One email column with a CHECK that no boundary value satisfies. -/
def oneChecked : Database := db! r"
  CREATE TABLE customers (email TEXT NOT NULL CHECK (instr(email, '@') > 1 AND length(email) >= 5));
  INSERT INTO customers VALUES ('ann@x.io');"

/-- An INTEGER PRIMARY KEY and an email. -/
def twoPlain : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, email TEXT NOT NULL);
  INSERT INTO customers VALUES (1, 'ann@x.io');"

/-- An INTEGER PRIMARY KEY and an email with a CHECK. -/
def twoChecked : Database := db! r"
  CREATE TABLE customers (
    id    INTEGER PRIMARY KEY,
    email TEXT NOT NULL CHECK (instr(email, '@') > 1 AND length(email) >= 5)
  );
  INSERT INTO customers VALUES (1, 'ann@x.io');"

labelled_sql "one-plain" in #sql_check Succeeds uniqueEmail
  (fun db => db.raw.catalog = onePlain.raw.catalog ∧ Holds noDuplicateEmails db) with (schema := onePlain)
labelled_sql "one-checked" in #sql_check Succeeds uniqueEmail
  (fun db => db.raw.catalog = oneChecked.raw.catalog ∧ Holds noDuplicateEmails db) with (schema := oneChecked)
labelled_sql "two-plain" in #sql_check Succeeds uniqueEmail
  (fun db => db.raw.catalog = twoPlain.raw.catalog ∧ Holds noDuplicateEmails db) with (schema := twoPlain)
labelled_sql "two-checked" in #sql_check Succeeds uniqueEmail
  (fun db => db.raw.catalog = twoChecked.raw.catalog ∧ Holds noDuplicateEmails db) with (schema := twoChecked)
labelled_sql "two-checked-db" in #sql_check uniqueEmail succeeds where noDuplicateEmails with (db := twoChecked)

/-- The schema of issue #293: no rows. -/
def customerSchema : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT NOT NULL);"

/-- An INSERT that fails when a customer with the id exists. -/
def insertCustomer : Script := sql! customerSchema r"
  INSERT INTO customers (id, name) VALUES (1, 'Grace');"

labelled_sql "primary-key" in #sql_check Succeeds insertCustomer
  (fun db => db.raw.catalog = customerSchema.raw.catalog) with (schema := customerSchema)

open Sampling in
#guard caseVariant (.text "ann@x.io".toUTF8.toList) == some (.text "Ann@x.io".toUTF8.toList)
open Sampling in
#guard caseVariant (.text "1@X".toUTF8.toList) == some (.text "1@x".toUTF8.toList)
open Sampling in
#guard caseVariant (.text "1@2".toUTF8.toList) == none
open Sampling in
#guard caseVariant (.integer 1) == none

/-- The text value of a string. -/
def textOf (text : String) : Value := .text text.toUTF8.toList

-- The variants of the row (1, 'ann@x.io'): the case variant and the same email again, each with the next
-- rowid in the INTEGER PRIMARY KEY. The email is NOT NULL, so no row has NULL.
#guard (Sampling.suppliedVariants twoChecked).map (fun database => (database.raw.rows.headD []).map (·.values)) ==
  [[[.integer 1, textOf "ann@x.io"], [.integer 2, textOf "Ann@x.io"]],
   [[.integer 1, textOf "ann@x.io"], [.integer 2, textOf "ann@x.io"]]]
