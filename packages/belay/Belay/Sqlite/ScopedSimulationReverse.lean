import Belay.Sqlite.ScopedSimulation

set_option doc.verso true

/-! The reverse direction of a scoped simulation (ADR 0017, S8). A pairing has an old and a new
interface. Its reverse pairing swaps the two. A scoped simulation of the pairing gives a scoped
simulation of the reverse pairing under the turned relation. That is a statement about the calls
only. A rollback also needs its own entry contract: a rollback migration must relate the reached
context to the context that it produces. The forward entry contract does not give it. -/

namespace Belay.Sqlite

open Belay.Sqlite.Calls

/-- The reverse of a pairing: the new interface becomes the old one, and the other way round. -/
def Calls.Pairing.swap {Name : Type} {signature : Signature Name} (pairing : Pairing signature) :
    Pairing signature :=
  ⟨pairing.new, pairing.old⟩

/-- The relation with its two arguments exchanged. -/
def ExecutionContext.turned (related : ExecutionContext → ExecutionContext → Prop) :
    ExecutionContext → ExecutionContext → Prop :=
  fun later earlier => related earlier later

namespace ScopedSimulation

variable {Name : Type} {signature : Signature Name}
  {related : ExecutionContext → ExecutionContext → Prop} {pairing : Pairing signature}

/-- A scoped simulation of a pairing under a relation is a scoped simulation of the reverse pairing
under the turned relation. Plain words: if each paired call agrees at every pair of related contexts,
then each reversed call agrees at every pair of contexts that are related the other way round. The
statement is about calls. It does not say that a rollback migration enters the turned relation.
Proof sketch: for a pair of turned-related contexts, the forward agreement at the swapped pair holds,
and {name}`Sql.ScopedAt.flip` turns it around. -/
theorem reverse (simulation : ScopedSimulation related pairing) :
    ScopedSimulation (ExecutionContext.turned related) pairing.swap :=
  fun name argument first second turned => (simulation name argument second first turned).flip

/-- Rollback safety, when its hypotheses hold. Take a scoped simulation of a pairing and a rollback
migration whose entry contract holds for the turned relation. Then for every application, every
context of the rollback domain and every returning rollback branch, the application in the new
interface, started at the original context, agrees with the application in the old interface, started
at the rolled-back context, under the turned relation. Proof sketch: {name}`ScopedSimulation.migrated`
for the reverse simulation. -/
theorem rolled_back {μ α : Type} {rollback : Sql μ} {admitted : ExecutionContext → Prop}
    (simulation : ScopedSimulation related pairing)
    (entry : MigrationEntry rollback admitted (ExecutionContext.turned related))
    (application : Application signature α) (state : ExecutionContext)
    (domain : Migration.Domain rollback admitted state) (run : SqlRun μ)
    (branch : rollback.Branch state.clock state.index state.connection run)
    (value : μ) (returned : run.value = some value) :
    Sql.ScopedAt (ExecutionContext.turned related) (application.interp pairing.new)
      (application.interp pairing.old) state ((Sql.View.quiet rollback).finish state run) :=
  simulation.reverse.migrated entry application state domain run branch value returned

end ScopedSimulation
end Belay.Sqlite
