import Belay.Sqlite.ExecutionViewEquivalenceBind
import Belay.Sqlite.ExecutionViewObservationBind

set_option doc.verso true

namespace Belay.Sqlite

/-- Uniform annotation of a bind annotates its prefix and every returned continuation
uniformly. Proof sketch: structural induction follows every output continuation. -/
theorem Sql.View.uniform_bind {α β : Type} (hidden : Bool) (program : Sql α) (next : α → Sql β) :
    uniform hidden (program.bind next) = (uniform hidden program).bind next (fun value => uniform hidden (next value)) := by
  induction program with
  | pure => rfl
  | exec statement values rest hypothesis =>
    simp only [Sql.bind, uniform, bind]
    exact congrArg (Sql.View.exec hidden) (funext hypothesis)

/-- Binding a view to pure returns leaves its projected trace unchanged for every
recorded trace. Proof sketch: structural induction on the view and trace. -/
theorem Sql.View.project_bind_pure {α : Type} {program : Sql α} (view : View program) (outputs : List Output) :
    (view.bind Sql.pure (fun value => .pure value)).project outputs = view.project outputs := by
  induction view generalizing outputs with
  | pure => rfl
  | exec hidden later hypothesis =>
    cases outputs with
    | nil => rfl
    | cons output outputs =>
      simp only [bind, project]
      split
      · rfl
      · rw [hypothesis output outputs]

/-- Reassociating three annotated segments retains every projected trace, including
result-dependent continuations and unmatched suffixes. Proof sketch: structural
induction on the first annotation follows the same recorded outputs. -/
theorem Sql.View.project_bind_assoc {α β γ : Type} {program : Sql α} (view : View program)
    (next : α → Sql β) (later : ∀ value, View (next value)) (last : β → Sql γ)
    (final : ∀ value, View (last value)) (outputs : List Output) :
    ((view.bind next later).bind last final).project outputs =
      (view.bind (fun value => (next value).bind last) (fun value => (later value).bind last final)).project outputs := by
  induction view generalizing outputs with
  | pure => rfl
  | exec hidden views hypothesis =>
    cases outputs with
    | nil => rfl
    | cons output outputs =>
      simp only [bind, project]
      split
      · rfl
      · rw [hypothesis output outputs]

/-- Views of equal programs compare fully if they project every permitted branch
trace equally. Actual execution is one of those branches. This explicitly supplies
the annotation correspondence that raw program equality alone cannot give.
Proof sketch: substitute the program equality, then match each identical raw result. -/
theorem Sql.View.equiv_of_program_eq {α : Type} {first second : Sql α}
    (left : View first) (right : View second) (programs : first = second) (state : ExecutionContext)
    (projections : ∀ result, first.Branch state.clock state.index state.connection result →
      left.project result.outputs = right.project result.outputs) : left.EquivAt right state := by
  subst second
  have observed result branch : left.fullObservation state result = right.fullObservation state result :=
    (fullObservation_eq_iff _ _ _ _ _).mpr ⟨Prod.ext rfl (projections result branch), rfl, rfl⟩
  exact observationProfile_transport (show first.EquivAt first state from rfl)
    (Sql.Branch.actual first _ _ _) (Sql.Branch.actual first _ _ _)
    (fun one two branch _ equal => by cases equal; exact observed one branch)

end Belay.Sqlite
