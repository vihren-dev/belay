import Belay

open Belay.Sqlite Lean Meta Elab

/-! The compiled screen of {lit}`#sql_check` ({lit}`Belay.Sqlite.Check.compileScreen`): a screen
that accepts every candidate gives no false result for a true claim, a claim with a compiled
override has no screen and is unknown with the reason, and a slow screen stops at
{lit}`sql.checkTimeLimit`. The test is {lit}`tests/surface_check_screen_test.py`. -/

/-- Mark the message of one command, so the test reads each block. -/
elab "labelled_sql " label:str " in " cmd:command : command => do
  logInfo m!"SQL-COMMAND-BEGIN {label.getString}"
  Command.elabCommand cmd
  logInfo m!"SQL-COMMAND-END {label.getString}:"

set_option maxHeartbeats 4000000

/-- A true claim: a query without tables does not fail on any database. -/
def selectOneSucceeds : Prop := ∀ db : Database, ¬ Fails (sql "SELECT 1") db

/-- A screen that accepts every candidate proposes only databases that the kernel rejects for a
true claim, so the result stays unknown. Proof automation is off, so that the search runs. -/
elab "check_accept_all_screen" : command => Command.liftTermElabM do
  let outcome ← Check.check (mkConst ``selectOneSucceeds) 200000
    { screen := some fun _ _ => true } (prove := fun _ => pure none)
  let .unknown := outcome.result | throwError "an accept-all screen changed the result of a true claim"
  logInfo "accept-all screen: unknown"

check_accept_all_screen

/-- A false claim: table {lit}`t` is missing or empty. -/
def noRows : Prop := ∀ db : Database, db.rows "t" = none ∨ db.rows "t" = some []

/-- A counterexample to {name}`noRows` with one row. -/
def withSeven : Database := db! "CREATE TABLE t(a); INSERT INTO t VALUES (7);"

/-- Shrinking with a screen certifies only its result. An accept-all screen shrinks the witness to
an empty table, which the kernel rejects, so the original witness stays; the compiled screen of
the claim shrinks the cell to NULL. -/
elab "check_screened_shrinking" : command => Command.liftTermElabM do
  let witnesses := #[{ database := mkConst ``withSeven }]
  let outcome ← Check.check (mkConst ``noRows) 200000
    { witnesses, screen := some fun _ _ => true } (prove := fun _ => pure none)
  let .refuted witness _ := outcome.result | throwError "the accept-all screen lost the counterexample"
  unless witness.database == mkConst ``withSeven do
    throwError "a shrink that the kernel rejects replaced the original witness"
  let outcome ← Check.check (mkConst ``noRows) 200000 { witnesses } (prove := fun _ => pure none)
  let .refuted witness _ := outcome.result | throwError "the compiled screen lost the counterexample"
  let database ← Check.databaseValue witness.database
  unless database.rows "t" == some [[.null]] do
    throwError "the compiled screen did not shrink the cell to NULL"
  logInfo "screened shrinking: original kept; shrunk to NULL"

check_screened_shrinking

/-- The logical value of the flag. -/
def plainFlag : Bool := true

/-- A flag with a compiled override. The checker does not run this code, so the claim has no
screen. -/
@[implemented_by plainFlag]
def overriddenFlag : Bool := true

/-- A false claim with the overridden flag. Its premise on table {lit}`t` rejects the empty
database, which the search tries without a screen. -/
def overrideClaim : Prop :=
  ∀ db : Database, (db.rows "t").isSome = true → overriddenFlag = true → Empty (sql "SELECT 1") db

labelled_sql "override" in #sql_check overrideClaim

labelled_sql "override-witness" in #sql_check overrideClaim with (db := db! "CREATE TABLE t(a);")

/-- Count down from the number, as a long loop of compiled code. -/
def countDown : Nat → Nat → Nat
  | 0, total => total
  | remaining + 1, total => countDown remaining (total + 1)

/-- A flag whose compiled computation takes much longer than the time limit below. It depends on
the database, so that the screen computes it and not the compilation. The claim below first
requires table {lit}`t`, so that the empty database, which the search certifies without the
screen, fails a cheap premise. -/
def slowFlag (db : Database) : Bool := countDown (20000000000 + db.raw.catalog.length) 0 > 0

set_option sql.checkTimeLimit 500 in
labelled_sql "slow" in #sql_check ∀ db : Database,
  (db.rows "t").isSome = true → slowFlag db = true → Empty (sql "SELECT 1") db
