import Belay.Sqlite.ExecutionViewEquivalence

set_option doc.verso true

namespace Belay.Sqlite

/-- Equal full observations at a shared starting context imply equal weak observations.
The shared prior trace cancels; return values stay equal. Proof sketch: project the
value and trace fields, then cancel the common trace prefix. -/
theorem Sql.View.observation_eq_of_full {α : Type} {first second : Sql α}
    (left : View first) (right : View second) (state : ExecutionContext)
    (one two : SqlRun α) (same : left.fullObservation state one = right.fullObservation state two) :
    left.observation one = right.observation two := by
  have value := congrArg Prod.fst same
  have outputs := congrArg (fun result => result.2.outputs) same
  have trace : left.project one.outputs = right.project two.outputs := List.append_cancel_left outputs
  exact Prod.ext value trace

/-- Full projected comparison implies weak comparison at the same context, for both
actual execution and every branch observation. Proof sketch: match a full observation
on the other side, then discard its non-trace context and common prior trace. -/
theorem Sql.View.EquivAt.observation {α : Type} {first second : Sql α}
    {left : View first} {right : View second} {state : ExecutionContext}
    (same : left.EquivAt right state) : left.ObservationEquivAt right state := by
  exact observationProfile_transport same (Sql.Branch.actual first _ _ _)
    (Sql.Branch.actual second _ _ _) (fun one two _ _ equal =>
      left.observation_eq_of_full right state one two equal)

end Belay.Sqlite
