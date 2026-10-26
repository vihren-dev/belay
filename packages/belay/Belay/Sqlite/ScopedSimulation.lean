import Belay.Sqlite.Application
import Belay.Sqlite.ScopedAgreementBind
import Belay.Sqlite.MigrationPattern

set_option doc.verso true

/-! Scoped simulation (ADR 0017, S8). Full-state simulation compares complete final contexts. That
fails when a migration changes a part of the context that the interface never reads, for example the
counter of changes that an extra trigger update raises. A scoped simulation names a relation between
an old-interface context and a new-interface context. It then asks that each paired call agree under
that relation: equal results and outputs, and related final contexts. -/

namespace Belay.Sqlite

open Belay.Sqlite.Calls

/-- A scoped simulation of a pairing under a relation between contexts. For every call name and
argument, the old call and its partner agree under the relation ({name}`Sql.ScopedOn`) at every pair of
related contexts. This gives the call conditions of the scoped claim:

* equal results and outputs, for the actual run and for every raw, concrete, errored or stopped branch,
  in both directions;
* related contexts after the call, so the relation is closed under every call;
* normal execution from each context's own clock, index and connection.

The relation is the invariant. It says which parts of the two contexts may differ. The claim does not
say that the final contexts are equal. -/
def ScopedSimulation {Name : Type} {signature : Signature Name}
    (related : ExecutionContext → ExecutionContext → Prop) (pairing : Pairing signature) : Prop :=
  ∀ name argument, Sql.ScopedOn related (pairing.old.run name argument) (pairing.new.run name argument)

/-- The entry contract of a migration for a relation. For every context where the migration
succeeds at the original context and the predicate holds ({name}`Migration.Domain`), and for every
branch of the migration that returns, the original context is related to the context that the
migration reaches. The migrated context is the one that the quiet view gives
({name}`Sql.View.finish`): the migration's successful outputs are hidden, and the raw statement
index counts every step of the migration. A migration that fails or stops is outside the domain and
requires nothing. -/
def MigrationEntry {μ : Type} (migration : Sql μ) (admitted : ExecutionContext → Prop)
    (related : ExecutionContext → ExecutionContext → Prop) : Prop :=
  ∀ state, Migration.Domain migration admitted state →
    ∀ run, migration.Branch state.clock state.index state.connection run →
      ∀ value, run.value = some value → related state ((Sql.View.quiet migration).finish state run)

namespace ScopedSimulation

variable {Name : Type} {signature : Signature Name}
  {related : ExecutionContext → ExecutionContext → Prop} {pairing : Pairing signature}

/-- For every scoped simulation and every application, the application in the old interface agrees
with the same application in the new interface under the relation, at every pair of related contexts.
Equal values and outputs and related final contexts hold for the actual run and every branch, in both
directions. Later calls and their arguments can depend on earlier results. The final contexts are
related, not equal. Proof sketch: induction on the application. A pure application uses
{name}`Sql.ScopedOn.pure`. A call uses {name}`Sql.ScopedOn.bind` with the call's own agreement and the
induction hypothesis for the continuation of each result. -/
theorem application (simulation : ScopedSimulation related pairing) {α : Type}
    (application : Application signature α) :
    Sql.ScopedOn related (application.interp pairing.old) (application.interp pairing.new) := by
  induction application with
  | pure value => exact Sql.ScopedOn.pure related value
  | call name argument rest hypothesis =>
    exact Sql.ScopedOn.bind (simulation name argument) hypothesis

/-- For every scoped simulation, every application and every migration with an entry contract for
the relation: at every context in the migration domain and at every returning migration branch, the
old application from the original context agrees with the new application from the migrated context,
under the relation. The migrated context is the one that the quiet view gives. The comparison is
about the new application after the migration, not about the migration after the old application. A
claim about the old application and then the migration needs a proved relation between the migrated
result of the old application and the final context of the new application. Proof sketch: the entry
contract relates the two start contexts, and {name}`ScopedSimulation.application` applies. -/
theorem migrated {μ α : Type} {migration : Sql μ} {admitted : ExecutionContext → Prop}
    (simulation : ScopedSimulation related pairing) (entry : MigrationEntry migration admitted related)
    (application : Application signature α) (state : ExecutionContext)
    (domain : Migration.Domain migration admitted state) (run : SqlRun μ)
    (branch : migration.Branch state.clock state.index state.connection run)
    (value : μ) (returned : run.value = some value) :
    Sql.ScopedAt related (application.interp pairing.old) (application.interp pairing.new) state
      ((Sql.View.quiet migration).finish state run) :=
  simulation.application application _ _ (entry state domain run branch value returned)

end ScopedSimulation
end Belay.Sqlite
