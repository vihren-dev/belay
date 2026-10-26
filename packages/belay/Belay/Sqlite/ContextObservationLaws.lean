import Belay.Sqlite.ContextObservation
import Belay.Sqlite.ExecutionFresh

set_option doc.verso true

/-!
Laws of the default and the real-context assertions: when they equal {lit}`Holds`, which output
cases establish them, and the validity of the database that a context sees at the end of a fresh
run.
-/

namespace Belay.Sqlite
open Model

/-- For every bundled database, environment, program and branch of the program from the fresh
initial connection, the database that the connection of the final context sees is valid under
the pinned profile. Proof sketch: the idle connection has no open-transaction snapshot, so the
start is valid; {name}`Sql.Branch.valid` keeps validity along the branch. -/
theorem ExecutionContext.initial_finish_valid {α : Type} {program : Sql α} (db : Database) {env : Env}
    {result : SqlRun α}
    (branch : program.Branch env.clock 0 (db.raw.connection env.counters) result) :
    ((ExecutionContext.initial db env).finish result).connection.state.database.Valid Profile.pinned :=
  (branch.valid ⟨db.valid, fun _ same => by simp [Database.Raw.connection] at same⟩).1

/-- For every query and context, the real-context assertion holds exactly when the observed
output exists and has rows in every result that SQLite may give. A query with no output, an
error, an unmodeled stop or an empty result does not establish it. Proof sketch: unfold the
assertion and split the optional output. -/
theorem Holds.inContext_iff {script : Script} {context : ExecutionContext}
    {query : script.isQuery = true} : Holds.inContext script context query ↔
      ∃ output, script.outputIn context = some output ∧ output.hasRows = true := by
  unfold Holds.inContext
  cases script.outputIn context <;> simp

/-- For every query, context and observed output without rows in some result (an empty
result, an error or an unmodeled stop), the real-context assertion does not hold.
Proof sketch: the observed output is unique, so its failing row test refutes the iff form. -/
theorem Holds.inContext_not {script : Script} {context : ExecutionContext}
    {query : script.isQuery = true} {output : Output} (observed : script.outputIn context = some output)
    (noRows : output.hasRows = false) : ¬ Holds.inContext script context query := by
  rw [Holds.inContext_iff]
  rintro ⟨seen, same, rows⟩
  rw [observed] at same
  cases same
  simp_all

/-- For every query and database, the default assertion at the default observation context of
the database is {name}`Holds`. The observation inputs are the same: no clock, unknown counters,
foreign keys off and no open transaction. Proof sketch: both unfold to the same run. -/
theorem Holds.inContext_observation_iff (script : Script) (db : Database) (query : script.isQuery = true) :
    Holds.inContext script db.raw.observationContext query ↔ Holds script db query := Iff.rfl

/-- For every query, context and bundled database that has the database the context sees, the
default assertion at the context equals {name}`Holds` on that database. The context's clock,
index, counters, settings, trace and open transaction do not matter. Proof sketch: after
replacing the database, both sides unfold to the run from its idle connection. -/
theorem Holds.reached_iff_holds (script : Script) (context : ExecutionContext) (db : Database)
    (query : script.isQuery = true) (sees : db.raw = context.connection.state.database) :
    Holds.reached script context query ↔ Holds script db query := by
  cases db with
  | mk raw valid =>
    simp only [] at sees
    subst sees
    exact Iff.rfl

/-- For every query, context and proof that the database the context sees is valid, the
default assertion at the context equals {name}`Holds` on that database as a bundled
database. For the final context of a fresh run, {name}`ExecutionContext.initial_finish_valid`
gives the proof, so no runtime validity test is needed. Proof sketch: the bundled database has
the visible database as its model database. -/
theorem Holds.reached_iff_holds_of_valid (script : Script) (context : ExecutionContext)
    (query : script.isQuery = true) (valid : context.connection.state.database.Valid Profile.pinned) :
    Holds.reached script context query ↔
      Holds script ⟨context.connection.state.database, valid⟩ query :=
  Holds.reached_iff_holds script context ⟨_, valid⟩ query rfl

/-- For every query, bundled database and environment, the default assertion at the initial
context of a fresh run is {name}`Holds` on the starting database. The environment's clock and
counters do not matter. Proof sketch: the initial context sees the starting database. -/
theorem Holds.reached_initial (script : Script) (db : Database) (env : Env)
    (query : script.isQuery = true) :
    Holds.reached script (ExecutionContext.initial db env) query ↔ Holds script db query :=
  Holds.reached_iff_holds script _ db query rfl

end Belay.Sqlite
