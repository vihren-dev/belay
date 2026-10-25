import Belay.Sqlite.ContextObservationBridge
import Belay.Sqlite.ExecutionBind
import Belay.Sqlite.DbBang
import Belay.Sqlite.SqlTerm

set_option doc.verso true
set_option maxRecDepth 4096

namespace AssertionExamples
open Belay.Sqlite Belay.Sqlite.Model Std.Do

/-- Two rows with an explicit rowid column. -/
def sample : Belay.Sqlite.Database := db! r"CREATE TABLE t(id INTEGER PRIMARY KEY, x INTEGER);
  INSERT INTO t VALUES (1, 1), (2, 2)"

/-- A complete environment with a distinct timestamp for each statement index. -/
def daily : Env :=
  { clock := some (fun index => 212602449600000 + 86400000 * index)
    counters := Counters.newConnection }

/-- The exact fresh starting context of these fixtures. -/
def initial : ExecutionContext := ExecutionContext.initial sample daily

/-- The context after one write that changed one row. -/
def afterWrite : ExecutionContext :=
  initial.finish ((send (sql r"INSERT INTO t VALUES (3, 3)")).runFrom daily.clock 0 initial.connection)

/-- The context after a pragma that switches foreign keys on. -/
def afterPragma : ExecutionContext :=
  initial.finish ((send (sql r"PRAGMA foreign_keys = ON")).runFrom daily.clock 0 initial.connection)

/-- The context inside an open transaction that inserted a third row. -/
def inTransaction : ExecutionContext :=
  initial.finish ((send (sql r"BEGIN; INSERT INTO t VALUES (3, 3)")).runFrom daily.clock 0 initial.connection)

/-- The context after a transaction that inserted a row and rolled it back. -/
def afterRollback : ExecutionContext :=
  initial.finish ((send (sql r"BEGIN; INSERT INTO t VALUES (3, 3); ROLLBACK")).runFrom daily.clock 0 initial.connection)

/-- A context that already holds a modeled SQL error in its trace. -/
def afterError : ExecutionContext := { initial with outputs := [.error 1] }

/-- A context that already holds an unmodeled stop in its trace. -/
def afterStop : ExecutionContext := { initial with outputs := [.unmodeled "earlier stop"] }

/-- The default observation context of a database is the context that {name}`Script.outputOn` uses. -/
theorem default_context_is_initial_observation :
    (ExecutionContext.initial sample daily).defaultObservation = sample.raw.observationContext := rfl

/-- The default assertion at the fresh context agrees with the plain {name}`Holds`. -/
theorem reached_matches_holds :
    Holds.reached (sql r"SELECT 1 FROM t WHERE id = 2") initial ↔
      Holds (sql r"SELECT 1 FROM t WHERE id = 2") sample := by decide +kernel

/-- A clock read holds in the context that has a clock, not in the default observation, which has none. -/
theorem clock_disagrees :
    Holds.inContext (sql r"SELECT CURRENT_TIMESTAMP IS NOT NULL") initial ∧
      ¬ Holds.reached (sql r"SELECT CURRENT_TIMESTAMP IS NOT NULL") initial := by decide +kernel

/-- A counter read sees the write in the real context and unknown counters in the default one. -/
theorem counters_disagree :
    Holds.inContext (sql r"SELECT 1 WHERE changes() = 1") afterWrite ∧
      ¬ Holds.reached (sql r"SELECT 1 WHERE changes() = 1") afterWrite := by decide +kernel

/-- A pragma query gives different outputs after the setting changed and in the default observation. -/
theorem pragma_outputs_differ :
    (sql r"PRAGMA foreign_keys").outputIn afterPragma = some (.rows [[1]]) ∧
      (sql r"PRAGMA foreign_keys").outputIn afterPragma.defaultObservation = some (.rows [[0]]) := by
  decide +kernel

/-- Inside an open transaction the default assertion sees the uncommitted row, as the context's database. -/
theorem transaction_row_visible :
    Holds.reached (sql r"SELECT 1 FROM t WHERE id = 3") inTransaction := by decide +kernel

/-- A rolled-back row is not visible to the default assertion. -/
theorem rollback_row_gone :
    ¬ Holds.reached (sql r"SELECT 1 FROM t WHERE id = 3") afterRollback ∧
    Holds.reached (sql r"SELECT 1 FROM t WHERE id = 2") afterRollback := by decide +kernel

/-- The same clock read gives different outputs at different statement indexes. -/
theorem clock_depends_on_index :
    (sql r"SELECT CURRENT_TIMESTAMP").outputIn initial ≠
      (sql r"SELECT CURRENT_TIMESTAMP").outputIn { initial with index := 3 } := by decide +kernel

/-- A default assertion does not fix the starting context: it holds at a later index, where a clock read does not. -/
theorem default_does_not_imply_fresh :
    ¬ (⦃fun context : ExecutionContext => ⌜Holds.reached (sql r"SELECT 1 FROM t WHERE id = 2") context⌝⦄
        Sql.pure () ⦃⇓ _ context => ⌜context.index = 0⌝⦄) := by
  intro triple
  have checked : (Sql.pure ()).check (fun _ context => context.index = 0) { initial with index := 5 } :=
    triple _ (by
      show Holds.reached (sql r"SELECT 1 FROM t WHERE id = 2") { initial with index := 5 }
      decide +kernel)
  have impossible : (5 : Nat) = 0 := (Sql.check_pure _ _ _).mp checked
  contradiction

#print axioms default_context_is_initial_observation
#print axioms reached_matches_holds
#print axioms clock_disagrees
#print axioms counters_disagree
#print axioms pragma_outputs_differ
#print axioms rollback_row_gone
#print axioms clock_depends_on_index
#print axioms transaction_row_visible
#print axioms default_does_not_imply_fresh
#print axioms Holds.reached_iff_holds
#print axioms Holds.inContext_iff_reached
#print axioms Script.outputIn_eq_of_independent
end AssertionExamples
