import Belay.Sqlite.MigrationPatternComposition

set_option doc.verso true

namespace Belay.Sqlite

/-- Equal continuation projections give equal projections after the same annotated
prefix, for every recorded trace and returned value. This statement concerns only
annotations, not equivalence of the underlying programs. Proof sketch: induction
on the shared view follows each recorded output to its continuation. -/
theorem Sql.View.project_bind_congr {α β : Type} {program : Sql α} (view : View program)
    (next other : α → Sql β) (later : ∀ value, View (next value))
    (last : ∀ value, View (other value))
    (equal : ∀ value outputs, (later value).project outputs = (last value).project outputs)
    (outputs : List Output) :
    (view.bind next later).project outputs = (view.bind other last).project outputs := by
  induction view generalizing outputs with
  | pure value => exact equal value outputs
  | exec hidden views hypothesis =>
    cases outputs with
    | nil => rfl
    | cons output outputs =>
      simp only [bind, project]
      split
      · rfl
      · rw [hypothesis output outputs]

namespace Migration

/-- Moving parentheses in an application before a migration retains the full
projected observation, including stopped branches and returned values. The second
application still depends on the first result. Proof sketch: program associativity
and annotation associativity give the same projection of every branch trace. -/
theorem before_bind {μ α β : Type} (migration : Sql μ) (application : Sql α)
    (next : α → Sql β) (state : ExecutionContext) :
    (beforeView (application.bind next) migration).EquivAt
      ((Sql.View.identity application).bind (fun value => before (next value) migration)
        (fun value => beforeView (next value) migration)) state := by
  apply Sql.View.equiv_of_program_eq _ _ (Sql.bind_assoc application next _) state
  intro result _
  simp only [beforeView, Sql.View.identity, Sql.View.uniform_bind]
  exact Sql.View.project_bind_assoc _ _ _ _ _ result.outputs

/-- Moving parentheses after a migration retains the complete projected result.
The application continuation receives the same value on every branch. Proof sketch:
program and annotation associativity identify the two executions and projections. -/
theorem after_bind {μ α β : Type} (migration : Sql μ) (application : Sql α)
    (next : α → Sql β) (state : ExecutionContext) :
    ((afterView migration application).bind next (fun value => Sql.View.identity (next value))).EquivAt
      (afterView migration (application.bind next)) state := by
  apply Sql.View.equiv_of_program_eq _ _ (Sql.bind_assoc migration (fun _ => application) next) state
  intro result _
  simp only [afterView, Sql.View.identity, Sql.View.uniform_bind]
  exact Sql.View.project_bind_assoc _ _ _ _ _ result.outputs

/-- An application, quiet migration and result-dependent continuation can be grouped
on either side of the migration. Remembering the application value adds no raw step.
Proof sketch: associate both binds and reduce the pure remembered return; annotation
associativity gives the same projection, even on stopped branches. -/
theorem before_then {μ α β : Type} (migration : Sql μ) (application : Sql α)
    (next : α → Sql β) (state : ExecutionContext) :
    ((beforeView application migration).bind next (fun value => Sql.View.identity (next value))).EquivAt
      ((Sql.View.identity application).bind (fun value => after migration (next value))
        (fun value => afterView migration (next value))) state := by
  refine Sql.View.equiv_of_program_eq _ _ ?_ state ?_
  · simp only [before, after, Sql.bind_assoc, Sql.bind]
  · intro result _
    exact (Sql.View.project_bind_assoc (Sql.View.identity application)
      (fun value => migration.bind fun _ => .pure value)
      (fun value => (Sql.View.quiet migration).bind (fun _ => .pure value) (fun _ => .pure value))
      next (fun value => Sql.View.identity (next value)) result.outputs).trans
      (Sql.View.project_bind_congr (Sql.View.identity application) _ _ _ _
        (fun value outputs => Sql.View.project_bind_assoc (Sql.View.quiet migration)
          (fun _ => .pure value) (fun _ => .pure value) next
          (fun value => Sql.View.identity (next value)) outputs) result.outputs)

end Migration
end Belay.Sqlite
