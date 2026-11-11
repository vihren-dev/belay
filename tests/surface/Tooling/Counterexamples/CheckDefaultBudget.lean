import Belay

open Belay.Sqlite Lean Meta Elab

/-! Claims of issue #317 that answer at the default {lit}`sql.checkBudget`, and the record of
accepted constants of the certificate audit ({lit}`Belay.Sqlite.Check.withAuditCache`). The test
is {lit}`tests/surface_check_default_budget_test.py`. -/

/-- Mark the message of one command, so the test reads each block. -/
elab "labelled_sql " label:str " in " cmd:command : command => do
  logInfo m!"SQL-COMMAND-BEGIN {label.getString}"
  Command.elabCommand cmd
  logInfo m!"SQL-COMMAND-END {label.getString}:"

set_option maxHeartbeats 4000000

/-- The guide's schema with two customers and three sessions: the variation of the rebuild that
#317 reports as unknown at the default budget. -/
def sample : Database := db! r"
  CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions(id INTEGER PRIMARY KEY, customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);
  INSERT INTO customers VALUES(1,'ada','Ada@X'),(2,'bob','bob@y');
  INSERT INTO sessions VALUES(10,1,100),(11,2,200),(12,2,300);"

/-- The rebuild with the pragma inside the transaction, on a connection that enforces foreign keys. -/
def requireNameWrongEnforced : Script := sql r"
  PRAGMA foreign_keys = ON;
  BEGIN;
  PRAGMA foreign_keys = OFF;
  CREATE TABLE customers_new (id INTEGER PRIMARY KEY, name TEXT NOT NULL, email TEXT NOT NULL);
  INSERT INTO customers_new SELECT id, name, email FROM customers;
  DROP TABLE customers;
  ALTER TABLE customers_new RENAME TO customers;
  COMMIT;"

/-- Every session. -/
def allSessions : Script := sql r"SELECT id, customer_id, expires_at FROM sessions"

labelled_sql "rebuild" in #sql_check requireNameWrongEnforced preserves allSessions with (db := sample)

/-- The declaration that the audits below exclude. -/
theorem auditExcluded : True := trivial

/-- A lemma that uses the excluded declaration. -/
theorem auditThrough : True := auditExcluded

/-- Whether the audit rejects the expressions with the exclusions. -/
def auditRejects (expressions : Array Expr) (excluded : Array Name) : MetaM Bool :=
  try Check.auditDependencies expressions excluded; pure false
  catch _ => pure true

#eval show MetaM Unit from do
  -- After the audit accepted other constants, a use of the excluded declaration through a lemma is rejected.
  Check.withAuditCache #[``auditExcluded] do
    if ← auditRejects #[mkConst ``True.intro, mkConst ``trivial] #[``auditExcluded] then
      throwError "the audit rejected constants without the excluded declaration"
    unless ← auditRejects #[mkConst ``auditThrough] #[``auditExcluded] do
      throwError "the audit accepted a use of the excluded declaration"
  -- A record made without exclusions is not used by an audit with exclusions.
  Check.withAuditCache #[] do
    if ← auditRejects #[mkConst ``auditThrough] #[] then
      throwError "the audit rejected the lemma without exclusions"
    unless ← auditRejects #[mkConst ``auditThrough] #[``auditExcluded] do
      throwError "the audit used a record made with other exclusions"
  IO.println "audit record checks passed"
