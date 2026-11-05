import Belay

open Belay.Sqlite Lean Elab

/-! The counterexample text of {lit}`#sql_check` for the claim that a unique index on a
{lit}`NOCASE` email succeeds where no two rows have equal emails: the search finds two emails
that differ only in case. The second claim gives an environment that is not the default, so
the text shows its values. The test is {lit}`tests/surface_check_readable_test.py`. -/

/-- Mark the message of one command, so the test reads each block. -/
elab "labelled_sql " label:str " in " cmd:command : command => do
  logInfo m!"SQL-COMMAND-BEGIN {label.getString}"
  Command.elabCommand cmd
  logInfo m!"SQL-COMMAND-END {label.getString}:"

set_option maxHeartbeats 4000000

def uniqueEmail := sql r"CREATE UNIQUE INDEX unique_email ON customers (email COLLATE NOCASE)"
def noDuplicateEmails : Script := sql r"
  SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM customers GROUP BY email HAVING count(*) > 1)"

-- The default budget does not reach the candidate with two emails.
set_option sql.checkBudget 2000000 in
labelled_sql "unique-email" in #sql_check uniqueEmail succeeds where noDuplicateEmails

labelled_sql "environment" in #sql_check ∀ db : Database, Empty (sql "SELECT 1") db
  with (env := { clockAt "2026-10-20 12:00:00" with counters := { changes := some 3 } })
