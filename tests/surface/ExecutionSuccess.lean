import ExecutionProofs
import Belay.Sqlite.ExecutionFresh

set_option doc.verso true
set_option maxRecDepth 4096

namespace ExecutionExamples
open Belay.Sqlite Std.Do

/-- A modeled error makes a false conditional property vacuous, while later writes still run. -/
theorem conditional_error :
    (send (sql r"SELECT absent FROM missing; INSERT INTO t VALUES (3, 3)")).ifOk
      (fun _ _ => False) initial := by decide +kernel

/-- The same error prevents total success even when the requested property is true. -/
theorem total_error :
    ¬ (send (sql r"SELECT absent FROM missing; INSERT INTO t VALUES (3, 3)")).andOk
      (fun _ _ => True) initial := by decide +kernel

/-- An error cannot make a later unmodeled step vacuous under the conditional policy. -/
theorem conditional_stop :
    ¬ (send (sql r"SELECT absent FROM missing; SELECT random()")).ifOk
      (fun _ _ => True) initial := by decide +kernel

/-- A fresh successful write satisfies both policies with its returned count and final rows. -/
theorem write_policies :
    writeOne.andOk (fun value state => value = 1 ∧
      (state.connection.state.database.rowsAt 0).length = 3) initial ∧
    writeOne.ifOk (fun value state => value = 1 ∧
      (state.connection.state.database.rowsAt 0).length = 3) initial := by decide +kernel

/-- Both kinds of non-OK prefix remove the conditional property even for a pure program. -/
theorem conditional_prefix :
    (Sql.pure ()).ifOk (fun _ _ => False) { initial with outputs := [.error 1] } ∧
    (Sql.pure ()).ifOk (fun _ _ => False) { initial with outputs := [.unmodeled "prior stop"] } := by
  decide +kernel

/-- Both kinds of non-OK prefix rule out total success, even though pure returns normally. -/
theorem total_prefix :
    ¬ (Sql.pure ()).andOk (fun _ _ => True) { initial with outputs := [.error 1] } ∧
    ¬ (Sql.pure ()).andOk (fun _ _ => True) { initial with outputs := [.unmodeled "prior stop"] } := by
  decide +kernel

/-- The S4 bridge uses the supplied index and connection even when they are not fresh. -/
theorem noninitial_bridge (program : Sql Nat) :
    program.andOk (fun _ _ => True) { initial with index := 7 } ↔
      program.SucceedsFrom daily.clock 7 initial.connection :=
  program.andOk_empty_iff _ rfl

/-- The total-success bridge still requires an unmodeled concrete alternative. -/
theorem total_alternate : ¬ alternateStops.andOk (fun _ _ => True) initial := by decide +kernel

/-- The total-success bridge still requires an unmodeled actual raw-wrapper continuation. -/
theorem total_raw : ¬ rawStops.andOk (fun _ _ => True) initial := by decide +kernel

/-- A fresh pure program retains its initial database, starts at zero and has an empty trace.
The postcondition can also use the same complete environment that the helper quantifies. -/
theorem fresh_pure : FreshTriple (Sql.pure (7 : Nat)) (fun _ => True)
    (fun db env value state => value = 7 ∧ state.index = 0 ∧ state.outputs = [] ∧
      state.connection = db.raw.connection env.counters ∧ env.Complete) := by
  intro db _ env complete
  rw [Sql.check_pure]
  exact ⟨rfl, rfl, rfl, rfl, complete⟩

/-- The fresh claim lifts to ordinary triples with exact database and environment entry facts. -/
theorem fresh_as_triples : ∀ db env,
    ⦃fun state : ExecutionContext => ⌜True ∧ env.Complete ∧ state = ExecutionContext.initial db env⌝⦄
      Sql.pure (7 : Nat) ⦃⇓ value state => ⌜value = 7 ∧ state.index = 0 ∧ state.outputs = [] ∧
        state.connection = db.raw.connection env.counters ∧ env.Complete⌝⦄ :=
  (FreshTriple.iff_triples _ _ _).mp fresh_pure

/-- Ordinary triples remain about all contexts: pure cannot establish index zero from True. -/
theorem arbitrary_context_is_not_fresh :
    ¬ (⦃fun _ : ExecutionContext => ⌜True⌝⦄ Sql.pure () ⦃⇓ _ state => ⌜state.index = 0⌝⦄) := by
  intro triple
  have checked : (Sql.pure ()).check (fun _ state => state.index = 0) { initial with index := 7 } :=
    triple _ True.intro
  have impossible : (7 : Nat) = 0 := (Sql.check_pure _ _ _).mp checked
  contradiction

/-- The public fresh bridge quantifies all complete environments, just as S4 does. -/
theorem universal_bridge (program : Sql Nat) (pre : Database → Prop) :
    FreshTriple program pre (fun _ _ _ state => state.outputs.allOk = true) ↔ Succeeds program pre :=
  FreshTriple.succeeds_iff program pre

#print axioms conditional_error
#print axioms total_error
#print axioms conditional_stop
#print axioms write_policies
#print axioms conditional_prefix
#print axioms total_prefix
#print axioms noninitial_bridge
#print axioms total_alternate
#print axioms total_raw
#print axioms fresh_pure
#print axioms fresh_as_triples
#print axioms arbitrary_context_is_not_fresh
#print axioms universal_bridge
#print axioms Sql.check_allOk_iff
#print axioms Sql.andOk_true_iff
#print axioms Sql.andOk_empty_iff
#print axioms Sql.andOk_ifOk
#print axioms Sql.andOk_complete_iff
#print axioms FreshTriple.iff_triples
#print axioms FreshTriple.branch
#print axioms FreshTriple.actual
#print axioms FreshTriple.succeeds_iff
end ExecutionExamples
