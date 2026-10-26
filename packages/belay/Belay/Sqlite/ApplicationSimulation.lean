import Belay.Sqlite.Application
import Belay.Sqlite.MigrationApplicationLaws

set_option doc.verso true

/-! Full-state simulation (ADR 0017, S8). A simulation says that every paired call of two
interfaces commutes with a migration in the full execution context: the connection, the clock, the
statement index and every branch outcome. Applications built from the calls then commute with the
migration as a whole. -/

namespace Belay.Sqlite

open Belay.Sqlite.Calls Belay.Sqlite.Migration

/-- A full-state simulation of a pairing by a migration over a context predicate. For every call name
and argument it requires two facts about the old call at the contexts that satisfy the predicate and
where the migration succeeds at the original context ({name}`Migration.Domain`).

* The call commutes with the migration ({name}`Migration.CommutesAsOn`): the old call and then the
  migration have the same projected actual run and branch outcomes as the migration and then the
  new call. Both orders return the call's result and keep the complete connection, the clock and the
  statement index. The projection hides only the outputs of the migration.
* The call keeps the domain: every branch of the old call that returns a value ends at a context that
  satisfies the predicate and where the migration succeeds. This includes a branch whose outputs hold a
  modeled SQL error, because the call still returns its result. Only a branch that stops without a
  value is exempt. -/
structure Simulation {Name : Type} {signature : Signature Name} {μ : Type} (migration : Sql μ)
    (admitted : ExecutionContext → Prop) (pairing : Pairing signature) : Prop where
  /-- Each old call commutes with the migration and has its partner as the replacement. -/
  commutes : ∀ name argument,
    CommutesAsOn migration admitted (pairing.old.run name argument) (pairing.new.run name argument)
  /-- Each old call keeps the context in the migration domain. -/
  keepsDomain : ∀ name argument,
    (pairing.old.run name argument).ReturnsIn (Domain migration admitted) (fun _ => Domain migration admitted)

namespace Simulation

variable {Name : Type} {signature : Signature Name} {μ : Type} {migration : Sql μ}
  {admitted : ExecutionContext → Prop} {pairing : Pairing signature}

/-- For every full-state simulation and every application, the application in the old interface
commutes with the migration, with the same application in the new interface as its replacement. The
conclusion has the meaning of {name}`Simulation.commutes` for a whole program: both orders return the
application's value and keep the complete final connection, clock, statement index and every actual,
raw and concrete branch, including stopped branches. Later calls and their arguments can depend on
earlier results. Proof sketch: induction on the application. A pure application uses
{name}`Migration.commutes_pure_application`. A call uses {name}`Migration.CommutesAsOn.bind` with the
call's own commutation, the induction hypothesis for each continuation, and domain preservation. -/
theorem commutes_application (simulation : Simulation migration admitted pairing) {α : Type}
    (application : Application signature α) :
    CommutesAsOn migration admitted (application.interp pairing.old) (application.interp pairing.new) := by
  induction application with
  | pure value => exact commutes_pure_application migration value admitted
  | call name argument rest hypothesis =>
    exact CommutesAsOn.bind (simulation.commutes name argument) hypothesis (simulation.keepsDomain name argument)

/-- For every full-state simulation, every application, every database that satisfies the database
predicate and every complete environment, if the initial context satisfies the context predicate,
the application commutes fully with the migration from the fresh run. The migration must succeed on
the original database for the comparison to apply. -/
theorem commutesAs_fresh (simulation : Simulation migration admitted pairing) {α : Type}
    (application : Application signature α) (admittedDatabase : Database → Prop)
    (fresh : ∀ db, admittedDatabase db → ∀ env : Env, env.Complete → admitted (ExecutionContext.initial db env)) :
    CommutesAs migration (application.interp pairing.old) (application.interp pairing.new) admittedDatabase := by
  intro db entry env complete state
  exact simulation.commutes_application application _ ⟨fresh db entry env complete, state.2⟩

end Simulation
end Belay.Sqlite
