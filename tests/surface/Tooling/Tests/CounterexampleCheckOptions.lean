import Belay

open Belay.Sqlite Lean Meta Elab
set_option maxHeartbeats 2000000
set_option sql.checkBudget 300000
set_option sql.checkShrinkAttempts 0
set_option sql.checkMaxRows 1
set_option sql.checkRandomSamples 1

/-! Check frontend options through actual search and replay. The row {lit}`(-1, NULL)` has
different values in its columns, so only the seeded random databases contain it: the targeted
databases and the small table contents repeat one value in every column of a row. -/

/-- Label the actual command's result for replay and outcome assertions. -/
elab "option_case " label:str " in " cmd:command : command => do
  logInfo m!"OPTION-BEGIN {label.getString}"
  Command.elabCommand cmd
  logInfo m!"OPTION-END {label.getString}"

/-- For every database, table t is not exactly one row with integer -1 and NULL.
This false claim requires a row that only the seeded random databases contain. -/
def randomOnly : Prop := ∀ db : Database, db.rows "t" ≠ some [[Value.integer (-1), .null]]

/-- The schema of the search: one table with two columns. -/
def twoColumns : Database := db! "CREATE TABLE t(a, b);"

set_option sql.checkSeed 13 in
option_case "seed-13" in #sql_check randomOnly with (schema := twoColumns)
set_option sql.checkSeed 0 in
option_case "seed-0" in #sql_check randomOnly with (schema := twoColumns)
set_option sql.checkSeed 13 in
set_option sql.checkRandomSamples 0 in
option_case "no-random" in #sql_check randomOnly with (schema := twoColumns)
set_option sql.checkSeed 12 in
option_case "one-random" in #sql_check randomOnly with (schema := twoColumns)
set_option sql.checkSeed 12 in
set_option sql.checkRandomSamples 2 in
option_case "two-random" in #sql_check randomOnly with (schema := twoColumns)
set_option sql.checkSeed 13 in
set_option sql.checkMaxRows 0 in
option_case "no-rows" in #sql_check randomOnly with (schema := twoColumns)

/-- Every database has no table t or has no rows in t. A nonempty table refutes this
claim; deleting its only row fails, then shrinking its cell to NULL keeps a counterexample. -/
def noRows : Prop := ∀ db : Database, db.rows "t" = none ∨ db.rows "t" = some []

set_option sql.checkCandidates 1 in
option_case "no-shrink" in #sql_check noRows with
  (db := db! "CREATE TABLE t(a); INSERT INTO t VALUES (7);")
set_option sql.checkCandidates 1 in
set_option sql.checkShrinkAttempts 2 in
option_case "two-shrinks" in #sql_check noRows with
  (db := db! "CREATE TABLE t(a); INSERT INTO t VALUES (7);")

/-- The configured size reaches a size-sensitive custom generator. Default fixed-bound
SQL generators do not use size to change their distribution. -/
elab "check_sized_candidate " expected:num : command => Command.runTermElabM fun _ => do
  let samples := Check.configuredSamples (← getOptions)
  let generator : Plausible.Gen (Option Database) := do
    let size ← Plausible.Gen.getSize
    return Sampling.uniform Sampling.defaultSchema [.integer (Int.ofNat size)]
  let .ok (some database) := Sampling.seeded generator samples.seed samples.size
    | throwError "the size-sensitive generator did not produce a database"
  unless database.rows "t" == some [[.integer (Int.ofNat expected.getNat)]] do
    throwError "the configured size did not reach the custom generator"
  let witness : Check.Witness := { database := databaseExpr database.raw }
  let outcome ← Check.check (mkConst ``noRows) 300000
    { samples with witnesses := #[witness], candidates := 1 } 0
  let .refuted _ proof := outcome.result | throwError "the sized proposal was not certified"
  discard <| Check.certify (mkNot (mkConst ``noRows)) proof
  logInfo m!"sized candidate certified with row {expected.getNat}"

set_option sql.checkSize 7 in check_sized_candidate 7
set_option sql.checkSize 9 in check_sized_candidate 9
