import Belay

/-! Query success retains prepare errors, execution errors and unmodeled outputs. Universal
proofs use the query and environment laws; kernel instances exercise both sides of the iff. -/

open Belay.Sqlite

/-- A constant SELECT succeeds for every database and every complete environment. -/
theorem select_one_success : (sql r"SELECT 1" succeeds) :=
  Succeeds.of_holds (query := by rfl) fun _ _ => rfl

/-- The query success equivalence does not unfold the interpreter in a caller's proof. -/
theorem query_success_cases (db : Database) (q : Script) (query : q.isQuery = true) :
    (db.run q).outputs.allOk = true ↔
      ¬ Fails q db query ∧ (q.outputOn db).any Output.endsRun = false :=
  Script.query_allOk_iff query db

/-- A successful default run is sufficient in any environment, including incomplete ones. -/
example (db : Database) (script : Script) (env : Env)
    (success : (db.run script).outputs.allOk = true) :
    (db.run script env).outputs.allOk = true := Script.allOk_env success env

/-- A small database for nonvacuity checks. -/
def sample : Database := db! r"CREATE TABLE t (x INTEGER); INSERT INTO t VALUES (1)"

example : (sample.run (sql r"SELECT x FROM t")).outputs.allOk = true ∧
    ¬ Fails (sql r"SELECT x FROM t") sample ∧
    ((sql r"SELECT x FROM t").outputOn sample).any Output.endsRun = false := by decide +kernel

example : (sample.run (sql r"SELECT x FROM t WHERE 0")).outputs.allOk = true ∧
    ¬ Fails (sql r"SELECT x FROM t WHERE 0") sample ∧
    ((sql r"SELECT x FROM t WHERE 0").outputOn sample).any Output.endsRun = false := by decide +kernel

example : (sample.run (sql r"SELECT x FROM missing")).outputs.allOk = false ∧
    ¬ (¬ Fails (sql r"SELECT x FROM missing") sample ∧
      ((sql r"SELECT x FROM missing").outputOn sample).any Output.endsRun = false) := by decide +kernel

example : (sample.run (sql r"SELECT abs(-9223372036854775808)")).outputs.allOk = false ∧
    ¬ (¬ Fails (sql r"SELECT abs(-9223372036854775808)") sample ∧
      ((sql r"SELECT abs(-9223372036854775808)").outputOn sample).any Output.endsRun = false) := by decide +kernel

example : (sample.run (sql r"SELECT CURRENT_TIMESTAMP")).outputs.allOk = false ∧
    ¬ (¬ Fails (sql r"SELECT CURRENT_TIMESTAMP") sample ∧
      ((sql r"SELECT CURRENT_TIMESTAMP").outputOn sample).any Output.endsRun = false) := by decide +kernel

/-- Supplying a clock succeeds where the same default run ends without an error.
This is why the query equivalence describes the default run. -/
example : (sample.run (sql r"SELECT CURRENT_TIMESTAMP")).outputs.allOk = false ∧
    (sample.run (sql r"SELECT CURRENT_TIMESTAMP") (clockAt "2026-10-20 12:00:00")).outputs.allOk = true := by
  decide +kernel

#print axioms select_one_success
#print axioms query_success_cases
