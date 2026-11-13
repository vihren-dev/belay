import Belay

open Belay.Sqlite Lean Elab

/-! Schemas that are the database at the end of a run of SQL text (issue #371): {lit}`#sql_check`
finds a replayable counterexample on such a schema ({lit}`Belay.Sqlite.Check.schemaText?`), with
{lit}`with (schema := ...)` and with the {lit}`on` form of a migration claim. A schema without SQL
text gives unknown with the reason. Each schema has an index, so the replay must build the schema
from its text. The test is {lit}`tests/surface_check_run_schemas_test.py`. -/

/-- Mark the message of one command, so the test reads each block. -/
elab "labelled_sql " label:str " in " cmd:command : command => do
  logInfo m!"SQL-COMMAND-BEGIN {label.getString}"
  Command.elabCommand cmd
  logInfo m!"SQL-COMMAND-END {label.getString}:"

set_option belay.sql.packageRoot "."

/-- The schema of a run of an SQL file on the empty database. -/
def fromFile : Database := (Database.empty.run (sql_file "sql_files/customers.sql")).db

/-- A {lit}`db!` schema, then a run of SQL text that adds an index. -/
def fromTwoRuns : Database :=
  ((db! r"CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);").run
    (sql r"CREATE INDEX customers_by_email ON customers(email);")).db

/-- A first run whose text ends with a comment and no semicolon, then a run that adds an index. The text of
the schema separates the two texts, so the last statement of the first text ends. -/
def fromUnterminated : Database :=
  ((Database.empty.run (sql r"CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL)
    -- no semicolon")).db.run (sql r"CREATE INDEX customers_by_email ON customers(email);")).db

/-- The schema of {name}`fromTwoRuns` after a run of a Lean program, which has no SQL text. -/
def withoutText : Database := (fromTwoRuns.run (Sql.pure ())).db

/-- A migration that adds a column, which changes the rows of {name}`allCustomers`. -/
def addEmailLower : Script := sql r"
ALTER TABLE customers ADD COLUMN email_lower TEXT;
UPDATE customers SET email_lower = lower(email);"

/-- Every row of the table. -/
def allCustomers : Script := sql r"SELECT * FROM customers"

labelled_sql "file-schema" in
#sql_check addEmailLower preserves allCustomers with (schema := fromFile)

labelled_sql "file-on" in
#sql_check addEmailLower preserves allCustomers on fromFile

labelled_sql "two-runs-on" in
#sql_check addEmailLower preserves allCustomers on fromTwoRuns

labelled_sql "unterminated-on" in
#sql_check addEmailLower preserves allCustomers on fromUnterminated

labelled_sql "without-text" in
#sql_check addEmailLower preserves allCustomers on withoutText
