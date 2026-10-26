import ApplicationShop

/-! A fixture of `tests/surface_application_test.py`: the two simulation theorems for the shop
applications (ADR 0017, S8). A full-state simulation by a pure migration and a scoped simulation
under a relation that ignores the earlier outputs hold for every application, including one that
chooses its later call from an earlier result. The scoped agreement fails for a different output, a
different value and an unrelated final context. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace ApplicationInterfaceFixture
open Belay.Sqlite Belay.Sqlite.Calls
open Belay.Sqlite.Model hiding Database

/-- A full-state simulation of the shop by a pure migration, with the same interface on both sides. -/
theorem pure_migration_simulates :
    Simulation (Sql.pure ()) (fun _ => True) (⟨oldShop, oldShop⟩ : Pairing shopSignature) :=
  ⟨fun _ _ => Migration.commutes_pure_migration () _ _,
    fun _ _ _ _ _ _ _ _ => ⟨True.intro, True.intro⟩⟩

/-- Every application commutes fully with the pure migration, whatever calls it chooses from earlier
results. -/
theorem every_application_commutes {α : Type} (application : Application shopSignature α) :
    Migration.CommutesAsOn (Sql.pure ()) (fun _ => True) (application.interp oldShop)
      (application.interp oldShop) :=
  pure_migration_simulates.commutes_application application

/-- Contexts that start the next statement in the same way: they agree on the clock, the index and
the connection, and may differ in the earlier outputs. -/
def sameStart (first second : ExecutionContext) : Prop :=
  first.clock = second.clock ∧ first.index = second.index ∧ first.connection = second.connection

/-- A scoped simulation of the shop under {name}`sameStart`: each call is its own partner. -/
theorem shop_scoped : ScopedSimulation sameStart (⟨oldShop, oldShop⟩ : Pairing shopSignature) :=
  fun name argument => Sql.ScopedOn.same_program sameStart _ (fun _ _ same => same)
    (fun first second result same => by
      obtain ⟨clock, index, -⟩ := same
      exact ⟨clock, by simp [ExecutionContext.finish, index], rfl⟩)

/-- The scoped theorem for an application that chooses its later call from an earlier result. -/
theorem welcome_scoped (id : Int64) (name : String) :
    Sql.ScopedOn sameStart ((welcome id name).interp oldShop) ((welcome id name).interp oldShop) :=
  shop_scoped.application (welcome id name)

/-- Two queries whose actual outputs differ do not agree at the first context of the sample, whatever
relation is used: the agreement requires equal outputs. Proof sketch: kernel evaluation of the two
runs. -/
theorem different_outputs_do_not_agree :
    ¬ Sql.ScopedAt (fun _ _ => True) (send (sql r"SELECT 1")) (send (sql r"SELECT 2")) initial initial := by
  intro agree
  have outputs := agree.actual.2.1
  revert outputs
  decide +kernel

/-- Two programs that return different values do not agree, although their outputs are equal. Proof
sketch: the agreement requires equal values; kernel evaluation of the two runs. -/
theorem different_values_do_not_agree :
    ¬ Sql.ScopedAt (fun _ _ => True) ((send (sql r"SELECT 1")).map fun _ => 1)
      ((send (sql r"SELECT 1")).map fun _ => 2) initial initial := by
  intro agree
  have values := agree.actual.1
  revert values
  decide +kernel

/-- A relation that fails for the contexts after a run makes the agreement fail, even when the runs
are equal. Here the relation holds only for the first context of the sample. Proof sketch: the
agreement requires the relation for the finished contexts; kernel evaluation shows that the finished
contexts differ from the first one. -/
theorem unrelated_final_contexts_do_not_agree :
    ¬ Sql.ScopedAt (fun first _ => first = initial) (send (sql r"SELECT 1")) (send (sql r"SELECT 1"))
      initial initial := by
  intro agree
  have reached := agree.actual.2.2
  simp only [ExecutionContext.finish, initial] at reached
  have index := congrArg ExecutionContext.index reached
  simp [ExecutionContext.initial] at index
  revert index
  decide +kernel

#print axioms pure_migration_simulates
#print axioms every_application_commutes
#print axioms shop_scoped
#print axioms welcome_scoped
#print axioms different_outputs_do_not_agree
#print axioms different_values_do_not_agree
#print axioms unrelated_final_contexts_do_not_agree

end ApplicationInterfaceFixture
