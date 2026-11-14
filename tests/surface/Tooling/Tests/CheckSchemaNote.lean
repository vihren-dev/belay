import Belay

open Belay.Sqlite Lean Elab

/-! The note of {lit}`#sql_check` for a search schema that only directs the search (issue #375,
{lit}`Belay.Sqlite.schemaOnlyDirectsNote`). The claim that {lit}`addEmailLower` keeps the result of
{lit}`namedCustomers` is false on a database whose table has a trigger that deletes the rows, so for every
database its answer is unknown, and {lit}`with (schema := shop)` gets the note. The claim with
{lit}`on shop`, a false answer and a search schema from {lit}`(db := shop)` get no note. The test is
{lit}`tests/surface_check_schema_note_test.py`. -/

/-- Mark the message of one command, so the test reads each block. -/
elab "labelled_sql " label:str " in " cmd:command : command => do
  logInfo m!"SQL-COMMAND-BEGIN {label.getString}"
  Command.elabCommand cmd
  logInfo m!"SQL-COMMAND-END {label.getString}:"

/-- The schema: one table of customers. -/
def shop : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);"

/-- A migration that adds a column and fills it from another column of the row. -/
def addEmailLower : Script := sql r"
ALTER TABLE customers ADD COLUMN email_lower TEXT;
UPDATE customers SET email_lower = lower(email);"

/-- A read with named columns, whose result the migration keeps on the databases of {name}`shop`. -/
def namedCustomers : Script := sql r"SELECT id, name, email FROM customers"

/-- A read whose result gets the new column. -/
def allCustomers : Script := sql r"SELECT * FROM customers"

set_option sql.checkCandidates 4

labelled_sql "with-schema" in
#sql_check addEmailLower preserves namedCustomers with (schema := shop)

labelled_sql "on-schema" in
#sql_check addEmailLower preserves namedCustomers on shop

labelled_sql "with-db" in
#sql_check addEmailLower preserves namedCustomers with (db := shop)

labelled_sql "false" in
#sql_check addEmailLower preserves allCustomers with (schema := shop)
