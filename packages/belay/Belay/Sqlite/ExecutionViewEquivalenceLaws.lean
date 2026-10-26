import Belay.Sqlite.ExecutionViewEquivalence

set_option doc.verso true

namespace Belay.Sqlite

/-- Each view has its own weak observations at every context.
Proof sketch: equality and branch-observation membership are reflexive. -/
theorem Sql.View.ObservationEquivAt.refl {α : Type} {program : Sql α}
    (view : View program) (state : ExecutionContext) : view.ObservationEquivAt view state :=
  ⟨rfl, fun _ => Iff.rfl⟩

/-- Weak projected comparison is symmetric at the same context.
Proof sketch: reverse actual equality and each observation-membership equivalence. -/
theorem Sql.View.ObservationEquivAt.symm {α : Type} {first second : Sql α}
    {left : View first} {right : View second} {state : ExecutionContext}
    (same : left.ObservationEquivAt right state) : right.ObservationEquivAt left state :=
  ⟨same.actual.symm, fun observation => (same.branches observation).symm⟩

/-- Weak comparisons compose at one context when both use the same middle program
and descriptor. Proof sketch: compose actual equality and observation membership. -/
theorem Sql.View.ObservationEquivAt.trans {α : Type} {first second third : Sql α}
    {left : View first} {middle : View second} {right : View third} {state : ExecutionContext}
    (one : left.ObservationEquivAt middle state) (two : middle.ObservationEquivAt right state) :
    left.ObservationEquivAt right state :=
  ⟨one.actual.trans two.actual, fun observation => (one.branches observation).trans (two.branches observation)⟩

/-- Each view has its own full observations at every context.
Proof sketch: equality and branch-observation membership are reflexive. -/
theorem Sql.View.EquivAt.refl {α : Type} {program : Sql α}
    (view : View program) (state : ExecutionContext) : view.EquivAt view state :=
  ⟨rfl, fun _ => Iff.rfl⟩

/-- Full projected comparison is symmetric at the same context.
Proof sketch: reverse actual equality and each observation-membership equivalence. -/
theorem Sql.View.EquivAt.symm {α : Type} {first second : Sql α}
    {left : View first} {right : View second} {state : ExecutionContext}
    (same : left.EquivAt right state) : right.EquivAt left state :=
  ⟨same.actual.symm, fun observation => (same.branches observation).symm⟩

/-- Full comparisons compose at one context with the same middle program and view.
Proof sketch: compose actual equality and full-observation membership. -/
theorem Sql.View.EquivAt.trans {α : Type} {first second third : Sql α}
    {left : View first} {middle : View second} {right : View third} {state : ExecutionContext}
    (one : left.EquivAt middle state) (two : middle.EquivAt right state) :
    left.EquivAt right state :=
  ⟨one.actual.trans two.actual, fun observation => (one.branches observation).trans (two.branches observation)⟩

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
  refine ⟨left.observation_eq_of_full right state _ _ same.actual, ?_⟩
  intro observation
  constructor
  · rintro ⟨result, branch, seen⟩
    obtain ⟨other, matched, equal⟩ := (same.branches _).mp ⟨result, branch, rfl⟩
    exact ⟨other, matched, (right.observation_eq_of_full left state _ _ equal).trans seen⟩
  · rintro ⟨result, branch, seen⟩
    obtain ⟨other, matched, equal⟩ := (same.branches _).mpr ⟨result, branch, rfl⟩
    exact ⟨other, matched, (left.observation_eq_of_full right state _ _ equal).trans seen⟩

end Belay.Sqlite
