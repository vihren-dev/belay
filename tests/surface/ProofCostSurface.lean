import Belay
import Belay.Sqlite.ProofCost
import ProofCostReader

/-! Three existing surface proof patterns provide the fixed overhead sample. The control compile
turns the option off; its proof text, positions and compiler are the same. -/
open Belay.Sqlite

set_option belay.proofCosts true

#proof_cost_begin

/-- A constant SELECT succeeds for every database and complete environment. -/
theorem constant_success : (sql r"SELECT 1" succeeds) :=
  Succeeds.of_holds (query := by rfl) fun _ _ => rfl

/-- A successful default run supplies success in any other environment. -/
theorem supplied_success (db : Database) (script : Script) (env : Env)
    (success : (db.run script).outputs.allOk = true) :
    (db.run script env).outputs.allOk = true := Script.allOk_env success env

/-- The default query result is successful exactly under the shared query condition. -/
theorem default_query (db : Database) (q : Script) (query : q.isQuery = true) :
    (db.run q).outputs.allOk = true ↔
      ¬ Fails q db query ∧ (q.outputOn db).any Output.endsRun = false :=
  Script.query_allOk_iff query db

#proof_cost_end
#print axioms constant_success
#print axioms supplied_success
#print axioms default_query
#proof_cost_records
#proof_cost_snapshot
