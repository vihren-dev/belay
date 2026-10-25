import Belay.Sqlite.MigrationApplicationViews
import Belay.Sqlite.MigrationPatternLaws

set_option doc.verso true

namespace Belay.Sqlite.Migration

/-- A pure migration commutes fully with every application on any context predicate.
It adds no step, output or connection effect. Proof sketch: the before view reduces
to the application's identity view followed by its unchanged pure return. -/
theorem commutes_pure_migration {μ α : Type} (value : μ) (application : Sql α)
    (pre : ExecutionContext → Prop) : CommutesOn (.pure value) pre application := by
  intro state _
  refine Sql.View.equiv_of_program_eq _ _ ?_ state ?_
  · change application.bind Sql.pure = application
    exact (Sql.bind_pure_map application id).trans (Sql.map_id application)
  · intro result _
    exact Sql.View.project_bind_pure (Sql.View.identity application) result.outputs

/-- A pure application commutes fully with every migration, retaining its chosen
return value. This holds on every original migration-success domain. Proof sketch:
both annotated executions reduce to the same migration followed by that pure value. -/
theorem commutes_pure_application {μ α : Type} (migration : Sql μ) (value : α)
    (pre : ExecutionContext → Prop) : CommutesOn migration pre (.pure value) := by
  intro state _
  exact Sql.View.EquivAt.refl _ state

/-- Full commutation composes across result-dependent application binds when every
returning original application branch reaches the next pattern's domain on its raw
context. That premise includes success of the migration there; it is a sufficient
law premise, not a change to the conclusion's original success domain. Both orders
retain the continuation's value and every actual, raw and concrete branch.
Proof sketch: commute the tail at the raw reached context, then commute the prefix
with the identical replacement continuation using full bind congruence. -/
theorem CommutesAsOn.bind {μ α β : Type} {migration : Sql μ}
    {application replacement : Sql α} {next other : α → Sql β}
    {pre : ExecutionContext → Prop} {post : α → ExecutionContext → Prop}
    (prefixes : CommutesAsOn migration pre application replacement)
    (tails : ∀ value, CommutesAsOn migration (post value) (next value) (other value))
    (reaches : application.ReturnsIn (Domain migration pre) (fun value => Domain migration (post value))) :
    CommutesAsOn migration pre (application.bind next) (replacement.bind other) := by
  have moveTail := Sql.View.EquivOn.bind
    (left := Sql.View.identity application) (right := Sql.View.identity application)
    (pre := Domain migration pre) (post := fun value => Domain migration (post value))
    (next := fun value => before (next value) migration)
    (other := fun value => after migration (other value))
    (later := fun value => beforeView (next value) migration)
    (last := fun value => afterView migration (other value))
    (fun state _ => Sql.View.EquivAt.refl _ state) tails reaches
  have movePrefix := Sql.View.EquivOn.bind
    (left := beforeView application migration) (right := afterView migration replacement)
    (pre := Domain migration pre) (post := fun _ _ => True)
    (next := other) (other := other)
    (later := fun value => Sql.View.identity (other value))
    (last := fun value => Sql.View.identity (other value))
    prefixes (fun _ state _ => Sql.View.EquivAt.refl _ state)
    (fun _ _ _ _ _ _ => True.intro)
  intro state entry
  exact (before_bind migration application next state).trans
    ((moveTail state entry).trans ((before_then migration application other state).symm.trans
      ((movePrefix state entry).trans (after_bind migration replacement other state))))

/-- Same-application commutation composes with the same raw reached-domain premise
as replacement commutation. Proof sketch: specialize {name}`CommutesAsOn.bind` to
identical programs in each position. -/
theorem CommutesOn.bind {μ α β : Type} {migration : Sql μ} {application : Sql α}
    {next : α → Sql β} {pre : ExecutionContext → Prop} {post : α → ExecutionContext → Prop}
    (prefixes : CommutesOn migration pre application)
    (tails : ∀ value, CommutesOn migration (post value) (next value))
    (reaches : application.ReturnsIn (Domain migration pre) (fun value => Domain migration (post value))) :
    CommutesOn migration pre (application.bind next) := CommutesAsOn.bind prefixes tails reaches

/-- Commutation over all supplied contexts still needs migration success at every
returning original application branch to use the tail pattern. Removing an explicit
predicate does not remove that obligation. Proof sketch: use true context predicates
in {name}`CommutesAsOn.bind`, retaining the raw reached success premise. -/
theorem CommutesAsOn.bind_unrestricted {μ α β : Type} {migration : Sql μ}
    {application replacement : Sql α} {next other : α → Sql β}
    (prefixes : CommutesAsOn migration (fun _ => True) application replacement)
    (tails : ∀ value, CommutesAsOn migration (fun _ => True) (next value) (other value))
    (reaches : application.ReturnsIn (Domain migration (fun _ => True))
      (fun _ => Domain migration (fun _ => True))) :
    CommutesAsOn migration (fun _ => True) (application.bind next) (replacement.bind other) :=
  CommutesAsOn.bind prefixes tails reaches

end Belay.Sqlite.Migration
