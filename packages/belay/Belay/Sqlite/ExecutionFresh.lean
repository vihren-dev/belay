import Belay.Sqlite.ExecutionSuccess
import Belay.Sqlite.ExecutionWPLaws

set_option doc.verso true

namespace Belay.Sqlite
open Belay.Sqlite Std.Do

/-- Every bundled valid database satisfying the precondition, and every complete environment,
starts this program with index zero, a new connection and an empty trace. Every branch must
return and satisfy the postcondition. The postcondition can retain the initial database and
environment; for example, it can compare initial and final rows. An unsatisfied precondition
requires nothing. Use ordinary triples when a caller supplies an existing context.
For total success require {lit}`final.outputs.allOk = true` with the final property; for
conditional success use it as the property's premise. Both policies still reject unmodeled
branches because this helper uses {name}`Sql.check`. -/
def FreshTriple {α : Type} (program : Sql α) (pre : Database → Prop)
    (post : Database → Env → α → ExecutionContext → Prop) : Prop :=
  ∀ db, pre db → ∀ env : Env, env.Complete →
    program.check (post db env) (ExecutionContext.initial db env)

/-- A fresh-run claim is exactly a family of ordinary triples, one per initial database and
environment. Each ordinary precondition requires the database predicate, a complete environment
and equality to its initial context. No other context is restricted. Proof sketch: specialize
in either direction at the same initial context; the context equality transports the check. -/
theorem FreshTriple.iff_triples {α : Type} (program : Sql α) (pre : Database → Prop)
    (post : Database → Env → α → ExecutionContext → Prop) :
    FreshTriple program pre post ↔ ∀ db env,
      ⦃fun state : ExecutionContext => ⌜pre db ∧ env.Complete ∧ state = ExecutionContext.initial db env⌝⦄
        program ⦃⇓ value state => ⌜post db env value state⌝⦄ := by
  constructor
  · intro checked db env state ⟨entry, complete, same⟩
    cases same
    exact checked db entry env complete
  · intro triples db entry env complete
    exact triples db env (ExecutionContext.initial db env) ⟨entry, complete, rfl⟩

/-- Every branch of a fresh triple returns a value satisfying its postcondition, at each
initial database satisfying the predicate and complete environment. The final context retains
the full trace and connection. Proof sketch: specialize the check and inspect its optional value. -/
theorem FreshTriple.branch {α : Type} {program : Sql α} {pre : Database → Prop}
    {post : Database → Env → α → ExecutionContext → Prop} (checked : FreshTriple program pre post)
    {db : Database} (entry : pre db) {env : Env} (complete : env.Complete) {result : SqlRun α}
    (branch : program.Branch env.clock 0 (db.raw.connection env.counters) result) :
    ∃ value, result.value = some value ∧
      post db env value ((ExecutionContext.initial db env).finish result) := by
  have holds := checked db entry env complete result branch
  cases returned : result.value with
  | none => simp [returned] at holds
  | some value => exact ⟨value, rfl, by simpa [returned] using holds⟩

/-- A fresh triple holds for the actual interpreter at each permitted database and complete
environment, and the interpreter returns. Proof sketch: actual-run membership supplies the branch. -/
theorem FreshTriple.actual {α : Type} {program : Sql α} {pre : Database → Prop}
    {post : Database → Env → α → ExecutionContext → Prop} (checked : FreshTriple program pre post)
    {db : Database} (entry : pre db) {env : Env} (complete : env.Complete) :
    ∃ value, (program.runFrom env.clock 0 (db.raw.connection env.counters)).value = some value ∧
      post db env value ((ExecutionContext.initial db env).finish
        (program.runFrom env.clock 0 (db.raw.connection env.counters))) :=
  checked.branch entry complete (Sql.Branch.actual program _ _ _)

/-- A fresh triple requiring only an error-free final trace is exactly S4 universal success.
Both sides quantify all valid bundled databases satisfying the predicate and every complete
environment, including raw and concrete continuations. Proof sketch: apply the empty-prefix
success bridge at each initial context. -/
theorem FreshTriple.succeeds_iff {α : Type} (program : Sql α) (pre : Database → Prop) :
    FreshTriple program pre (fun _ _ _ final => final.outputs.allOk = true) ↔ Succeeds program pre := by
  simpa [FreshTriple, Sql.andOk] using program.andOk_complete_iff pre

end Belay.Sqlite
