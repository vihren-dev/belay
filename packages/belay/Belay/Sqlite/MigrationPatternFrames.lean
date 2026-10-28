import Belay.Sqlite.MigrationPatternComposition

set_option doc.verso true

namespace Belay.Sqlite.Migration

/-- At the original migration-success context, weak translation implies full commutation
under three independent sufficient conditions. The migration succeeds after every
returning application branch; equal projected branch observations in the two orders
have equal COMPLETE connections; and those pairs execute equally many raw steps.
The connection condition covers counters, settings, snapshots, stored clock assignment
and the catalogs used for later resolution. External clock/index sensitivity must be
accounted for in these execution facts. Read-only syntax alone supplies none of them.
The premises cover all raw/concrete branches and hence the actual runs as well.
Proof sketch: remove the successful trailing migration from weak observation, apply
translation, then add the independent connection and step-count frames. -/
theorem TranslatesAt.commutes_of_frames {μ α : Type} {migration : Sql μ}
    {application replacement : Sql α} {pre : ExecutionContext → Prop} {state : ExecutionContext}
    (translation : TranslatesAt migration pre application replacement state)
    (laterSuccess : Domain migration pre state → ∀ result,
      application.Branch state.clock state.index state.connection result → ∀ value,
      result.value = some value →
        migration.SucceedsFrom state.clock (state.index + result.outputs.length) result.connection)
    (connections : Domain migration pre state → ∀ one two,
      (before application migration).Branch state.clock state.index state.connection one →
      (after migration replacement).Branch state.clock state.index state.connection two →
      (beforeView application migration).observation one = (afterView migration replacement).observation two →
        one.connection = two.connection)
    (steps : Domain migration pre state → ∀ one two,
      (before application migration).Branch state.clock state.index state.connection one →
      (after migration replacement).Branch state.clock state.index state.connection two →
      (beforeView application migration).observation one = (afterView migration replacement).observation two →
        one.outputs.length = two.outputs.length) :
    CommutesAsAt migration pre application replacement state := by
  intro entry
  exact Sql.View.ObservationEquivAt.full_of_frames
    ((before_observation migration application state (laterSuccess entry)).trans (translation entry))
    (connections entry) (steps entry)

/-- The fixed-context frame bridge applies at every context satisfying the original
migration domain when its three explicit premises hold there. No intermediate context
is replaced by a fresh environment. Proof sketch: specialize the fixed-context theorem. -/
theorem TranslatesOn.commutes_of_frames {μ α : Type} {migration : Sql μ}
    {application replacement : Sql α} {pre : ExecutionContext → Prop}
    (translation : TranslatesOn migration pre application replacement)
    (laterSuccess : application.ReturnsIn (Domain migration pre)
      (fun _ state => migration.SucceedsFrom state.clock state.index state.connection))
    (connections : ∀ state, Domain migration pre state → ∀ one two,
      (before application migration).Branch state.clock state.index state.connection one →
      (after migration replacement).Branch state.clock state.index state.connection two →
      (beforeView application migration).observation one = (afterView migration replacement).observation two →
        one.connection = two.connection)
    (steps : ∀ state, Domain migration pre state → ∀ one two,
      (before application migration).Branch state.clock state.index state.connection one →
      (after migration replacement).Branch state.clock state.index state.connection two →
      (beforeView application migration).observation one = (afterView migration replacement).observation two →
        one.outputs.length = two.outputs.length) :
    CommutesAsOn migration pre application replacement := by
  intro state
  exact (translation state).commutes_of_frames (laterSuccess state) (connections state) (steps state)

end Belay.Sqlite.Migration
