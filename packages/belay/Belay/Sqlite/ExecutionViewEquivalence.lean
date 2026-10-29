import Belay.Sqlite.ExecutionViewLaws
import Belay.Sqlite.ExecutionObservations

set_option doc.verso true

namespace Belay.Sqlite

/-- At one shared context, the views give equal actual return values and traces,
and exactly the same set of branch return values and traces. Final connections
are omitted. Errors and unmodeled stops remain visible through each view. Use
this weak comparison for observations that need not determine later execution. -/
def Sql.View.ObservationEquivAt {α : Type} {first second : Sql α}
    (left : View first) (right : View second) (state : ExecutionContext) : Prop :=
  observationProfile (first.runFrom state.clock state.index state.connection)
    (first.Branch state.clock state.index state.connection) (left.observation) =
  observationProfile (second.runFrom state.clock state.index state.connection)
    (second.Branch state.clock state.index state.connection) (right.observation)

/-- At one shared context, the views give equal actual full observations and
exactly the same set of branch full observations. Each observation retains the
optional value, projected trace, full connection, clock and raw next index.
Only the annotated successful outputs can be hidden; ordinary strong equivalence
still observes them. Use this relation when later SQL can inspect reached state. -/
def Sql.View.EquivAt {α : Type} {first second : Sql α}
    (left : View first) (right : View second) (state : ExecutionContext) : Prop :=
  observationProfile (first.runFrom state.clock state.index state.connection)
    (first.Branch state.clock state.index state.connection) (left.fullObservation state) =
  observationProfile (second.runFrom state.clock state.index state.connection)
    (second.Branch state.clock state.index state.connection) (right.fullObservation state)

/-- Weak projected comparison at every context satisfying the supplied predicate.
Contexts outside that domain require nothing; an empty domain is vacuous. -/
def Sql.View.ObservationEquivOn {α : Type} {first second : Sql α}
    (pre : ExecutionContext → Prop) (left : View first) (right : View second) : Prop :=
  ∀ state, pre state → left.ObservationEquivAt right state

/-- Full projected comparison at every context satisfying the supplied predicate.
The domain is explicit; composition must establish it at the relevant reached
contexts rather than resetting a connection or substituting a fresh environment. -/
def Sql.View.EquivOn {α : Type} {first second : Sql α}
    (pre : ExecutionContext → Prop) (left : View first) (right : View second) : Prop :=
  ∀ state, pre state → left.EquivAt right state

/-- Weak projected comparison at every shared context, without a domain restriction.
This relation alone does not justify replacing a prefix before arbitrary SQL. -/
def Sql.View.ObservationEquiv {α : Type} {first second : Sql α}
    (left : View first) (right : View second) : Prop := ∀ state, left.ObservationEquivAt right state

/-- Full projected comparison at every shared context. The exact descriptors are
part of the relation; a continuation comparison must account for those descriptors. -/
def Sql.View.Equiv {α : Type} {first second : Sql α}
    (left : View first) (right : View second) : Prop := ∀ state, left.EquivAt right state

end Belay.Sqlite
