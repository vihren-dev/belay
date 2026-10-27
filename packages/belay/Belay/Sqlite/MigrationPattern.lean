import Belay.Sqlite.ExecutionViewIdentity

set_option doc.verso true

namespace Belay.Sqlite.Migration

/-- The supplied predicate holds and the migration succeeds at this original context
on its actual and every raw/concrete branch. Earlier trace errors impose no extra
condition. A moved application can make the later migration fail without removing
this original context from the domain. Keep migration success as a separate claim. -/
def Domain {μ : Type} (migration : Sql μ) (pre : ExecutionContext → Prop)
    (state : ExecutionContext) : Prop :=
  pre state ∧ migration.SucceedsFrom state.clock state.index state.connection

/-- The domain of a migration is decidable when its predicate is and the migration is a finite program: the
decision runs the model, so a closed claim about the domain is certified by evaluation. -/
instance Domain.decidable {μ : Type} (migration : Sql μ) (pre : ExecutionContext → Prop)
    [DecidablePred pre] (state : ExecutionContext) : Decidable (Domain migration pre state) :=
  inferInstanceAs (Decidable (pre state ∧ migration.SucceedsFrom state.clock state.index state.connection))

/-- Run the migration, then the application, returning the application's value.
An unmodeled migration stop still returns none through the ordinary interpreter. -/
def after {μ α : Type} (migration : Sql μ) (application : Sql α) : Sql α :=
  migration.bind fun _ => application

/-- Observe the application after a quiet migration segment. The annotation keeps
all migration failures and the ordinary execution's returned application value. -/
def afterView {μ α : Type} (migration : Sql μ) (application : Sql α) : Sql.View (after migration application) :=
  (Sql.View.quiet migration).bind (fun _ => application) fun _ => Sql.View.identity application

/-- Run the application, then the migration, retaining the application's value
when both return. A migration stop gives no value, as in ordinary bind execution. -/
def before {μ α : Type} (application : Sql α) (migration : Sql μ) : Sql α :=
  application.bind fun value => migration.bind fun _ => .pure value

/-- Observe the application before a quiet migration, with a separate annotation
for every returned application value and every migration continuation. -/
def beforeView {μ α : Type} (application : Sql α) (migration : Sql μ) : Sql.View (before application migration) :=
  (Sql.View.identity application).bind _ fun value =>
    (Sql.View.quiet migration).bind (fun _ => .pure value) fun _ => .pure value

/-- At this original context, if the explicit predicate holds and the migration
succeeds, the original application and its replacement after the migration have
equal projected actual values/traces and branch observations. Final state is omitted.
If the original migration fails or the predicate is false, this proposition is vacuous.
This flexible primitive accepts arbitrary programs; query helpers add read-only admission. -/
def TranslatesAt {μ α : Type} (migration : Sql μ) (pre : ExecutionContext → Prop)
    (original replacement : Sql α) (state : ExecutionContext) : Prop :=
  Domain migration pre state →
    (Sql.View.identity original).ObservationEquivAt (afterView migration replacement) state

/-- Translation at every context in the original migration-success domain of the
supplied predicate. It compares query observations when the caller supplies queries;
the primitive also permits other programs without claiming state equivalence. -/
def TranslatesOn {μ α : Type} (migration : Sql μ) (pre : ExecutionContext → Prop)
    (original replacement : Sql α) : Prop := ∀ state, TranslatesAt migration pre original replacement state

/-- At this context the migration preserves the application's weak observations
on its original success domain: translation uses the same program on both sides.
Outside that domain it requires nothing. -/
def PreservesAt {μ α : Type} (migration : Sql μ) (pre : ExecutionContext → Prop)
    (application : Sql α) (state : ExecutionContext) : Prop := TranslatesAt migration pre application application state

/-- Preservation at every context satisfying the supplied predicate and original
migration success. The relation retains application values and errors, but not final state. -/
def PreservesOn {μ α : Type} (migration : Sql μ) (pre : ExecutionContext → Prop)
    (application : Sql α) : Prop := TranslatesOn migration pre application application

/-- On the original migration-success domain at this context, application-then-migration
and migration-then-replacement have equal projected full actual and branch observations.
Both orders return the application's value, and retain full connection, clock and raw
index. A failure introduced by moving the application remains observable and cannot
remove the original context from the domain. Success of that later migration is
not a domain premise. Outside the domain this is vacuous. -/
def CommutesAsAt {μ α : Type} (migration : Sql μ) (pre : ExecutionContext → Prop)
    (application replacement : Sql α) (state : ExecutionContext) : Prop :=
  Domain migration pre state → (beforeView application migration).EquivAt (afterView migration replacement) state

/-- Full contextual commutation with a replacement at every context satisfying the
explicit predicate and original migration success. No fresh-context reset is applied. -/
def CommutesAsOn {μ α : Type} (migration : Sql μ) (pre : ExecutionContext → Prop)
    (application replacement : Sql α) : Prop := ∀ state, CommutesAsAt migration pre application replacement state

/-- At this context, full commutation uses the same application in both orders,
on the explicit original migration-success domain. Outside it the claim is vacuous. -/
def CommutesAt {μ α : Type} (migration : Sql μ) (pre : ExecutionContext → Prop)
    (application : Sql α) (state : ExecutionContext) : Prop := CommutesAsAt migration pre application application state

/-- Full commutation with the same application at every context in the explicit
original migration-success domain. It retains counter and clock effects. -/
def CommutesOn {μ α : Type} (migration : Sql μ) (pre : ExecutionContext → Prop)
    (application : Sql α) : Prop := CommutesAsOn migration pre application application

end Belay.Sqlite.Migration
