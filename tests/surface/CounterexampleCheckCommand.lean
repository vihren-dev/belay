import Belay

open Belay.Sqlite Lean Elab

/-! Exercise the actual command, including its default proof-first path, finite options and
supplied inputs. Data premises prevent missing tables from replacing the intended boundaries. -/

/-- Measure complete command elaboration without asserting a machine-dependent time bound. -/
elab "measured_sql " label:str " in " cmd:command : command => do
  let started ← IO.monoMsNow
  let before ← IO.getNumHeartbeats
  logInfo m!"SQL-COMMAND-BEGIN {label.getString}"
  Command.elabCommand cmd
  logInfo m!"SQL-COMMAND-END {label.getString}: heartbeats={(← IO.getNumHeartbeats)-before}; elapsedMs={(← IO.monoMsNow)-started}"

set_option maxHeartbeats 2000000

section
variable (kernel : Nat)
measured_sql "proof" in #sql_check ∀ db : Database, kernel = kernel ∧ db = db
end
measured_sql "missing" in #sql_check ∀ db : Database, Holds (sql "SELECT 1 FROM absent") db
measured_sql "nonempty" in #sql_check ∀ db : Database, Empty (sql "SELECT 1") db
measured_sql "fails" in #sql_check ∀ db : Database, Fails (sql "SELECT 1") db
measured_sql "success" in #sql_check Succeeds (sql "INSERT INTO absent VALUES (1)") (fun _ => True)
measured_sql "parameter" in
#sql_check ∀ amount : Value, ∀ db : Database, Empty ((sql "SELECT :amount") amount) db
  with (input amount := Value.text [39])
measured_sql "plain" in #sql_check ∀ db : Database, db.rows "custom" = none
  with (schema := db! "CREATE TABLE custom(x);")

/-- The first candidate cannot establish this premise; the second must still be tried. -/
def selectedRows : Prop := ∀ db : Database, db.rows "t" = some [[Value.integer 7]] →
  Empty (sql "SELECT a FROM t") db
set_option sql.checkBudget 200000 in
set_option sql.checkCandidates 2 in
measured_sql "ordered" in #sql_check selectedRows with
  (db := Database.empty) (db := db! "CREATE TABLE t(a); INSERT INTO t VALUES (7);")

/-- The inferred people schema is part of each data-boundary claim. -/
def grouped : Script := sql "SELECT 1 FROM people GROUP BY address COLLATE NOCASE HAVING COUNT(*) > 1"
/-- Exact schema equality and named rows rule out missing-table witnesses. -/
def peopleSchema : Database := (Sampling.scriptHints grouped).schema.getD Database.empty
/-- ASCII a/A rows form one duplicate NOCASE group. -/
def asciiClaim : Prop := ∀ db : Database,
  db.raw.catalog = peopleSchema.raw.catalog →
  db.rows "people" = some [[Value.text [97]], [Value.text [65]]] → Empty grouped db
/-- Non-ASCII æ/Æ rows do not form a duplicate NOCASE group. -/
def unicodeClaim : Prop := ∀ db : Database,
  db.raw.catalog = peopleSchema.raw.catalog →
  db.rows "people" = some [[Value.text "æ".toUTF8.toList], [Value.text "Æ".toUTF8.toList]] → Holds grouped db
/-- Two bounded signed integers overflow when SUM adds them. -/
def aggregate : Script := sql "SELECT SUM(amount) FROM ledger"
/-- The ledger table and column are fixed before the overflow is checked. -/
def ledgerSchema : Database := (Sampling.scriptHints aggregate).schema.getD Database.empty
/-- This claim requires the intended two integers instead of permitting a missing table. -/
def overflowClaim : Prop := ∀ db : Database,
  db.raw.catalog = ledgerSchema.raw.catalog →
  db.rows "ledger" = some [[Value.integer 4611686018427387904], [Value.integer 4611686018427387904]] →
  Holds aggregate db

set_option sql.checkBudget 500000 in
measured_sql "nocase" in #sql_check asciiClaim
set_option sql.checkBudget 500000 in
measured_sql "nonascii" in #sql_check unicodeClaim
set_option sql.checkBudget 500000 in
measured_sql "overflow" in #sql_check overflowClaim

set_option sql.checkBudget 0 in
measured_sql "disabled" in #sql_check ∀ db : Database, Empty (sql "SELECT 1") db
set_option sql.checkCandidates 0 in
measured_sql "no-candidates" in #sql_check ∀ db : Database, Empty (sql "SELECT 1") db
set_option sql.checkRecursionLimit 128 in
set_option sql.checkCandidates 1 in
measured_sql "low-depth" in #sql_check ∀ db : Database, Empty (sql "SELECT 1") db
  with (db := Database.empty)
set_option sql.checkCandidates 1 in
measured_sql "unavailable" in #sql_check ∀ db : Database, Holds (sql "SELECT random()") db
  with (db := Database.empty)

measured_sql "after-limits" in #sql_check True
