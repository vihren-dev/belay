import Belay.Sqlite.ScopedSimulationReverse
import Belay.Sqlite.ApplicationSimulation

set_option doc.verso true

/-! The two simulation claims of a migration (ADR 0017, S8), side by side. A full-state claim is
{name}`Belay.Sqlite.Simulation`: each paired call commutes with the migration and every complete final context is
equal. A scoped claim is {lit}`ScopedClaim`: the migration enters a relation between contexts and each
paired call agrees under that relation. The scoped claim never says that the final contexts are equal.
The surface syntax {lit}`migration simulates pairing` and
{lit}`migration simulates pairing scoped by relation` elaborate to these two. -/

namespace Belay.Sqlite

open Belay.Sqlite.Calls

/-- The scoped claim of a migration for a pairing: the migration enters the relation, and the pairing
is a scoped simulation under the relation. In order:

* the entry contract {name}`MigrationEntry`: at every admitted context where the migration succeeds
  at the original context, every returning branch of the migration reaches a context that the relation
  relates to the original context;
* the call contract {name}`ScopedSimulation`: at every pair of related contexts, each paired call
  agrees (equal results and outputs, related final contexts, matching branches in both directions).

Nothing says that the final contexts of the two sides are equal. -/
structure ScopedClaim {Name : Type} {signature : Signature Name} {μ : Type} (migration : Sql μ)
    (admitted : ExecutionContext → Prop) (related : ExecutionContext → ExecutionContext → Prop)
    (pairing : Pairing signature) : Prop where
  /-- The migration enters the relation. -/
  entry : MigrationEntry migration admitted related
  /-- Each paired call agrees under the relation. -/
  calls : ScopedSimulation related pairing

/-- For every scoped claim and every application: at every admitted context where the migration
succeeds, and at every returning migration branch, the old application from the original context
agrees with the new application from the migrated context, under the relation. This is
{name}`ScopedSimulation.migrated` for the two parts of the claim. -/
theorem ScopedClaim.application {Name : Type} {signature : Signature Name} {μ α : Type}
    {migration : Sql μ} {admitted : ExecutionContext → Prop}
    {related : ExecutionContext → ExecutionContext → Prop} {pairing : Pairing signature}
    (claim : ScopedClaim migration admitted related pairing) (application : Application signature α)
    (state : ExecutionContext) (domain : Migration.Domain migration admitted state) (run : SqlRun μ)
    (branch : migration.Branch state.clock state.index state.connection run) (value : μ)
    (returned : run.value = some value) :
    Sql.ScopedAt related (application.interp pairing.old) (application.interp pairing.new) state
      ((Sql.View.quiet migration).finish state run) :=
  claim.calls.migrated claim.entry application state domain run branch value returned

end Belay.Sqlite
