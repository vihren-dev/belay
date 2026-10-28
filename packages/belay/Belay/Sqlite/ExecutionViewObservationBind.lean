import Belay.Sqlite.ExecutionViewBind
import Belay.Sqlite.ExecutionViewEquivalenceLaws

set_option doc.verso true

namespace Belay.Sqlite

/-- Equal weak tail observations concatenate equally after one fixed returning prefix.
The prefix remains the same execution branch and annotation. Proof sketch: apply the
projection concatenation law and keep the suffix's optional returned value. -/
theorem Sql.View.observation_bind_return_eq {α β : Type} {program : Sql α}
    (view : View program) {clock index connection first}
    (branch : program.Branch clock index connection first) {value : α} (returned : first.value = some value)
    (next other : α → Sql β) (later : ∀ value, View (next value)) (last : ∀ value, View (other value))
    (tail otherTail : SqlRun β) (same : (later value).observation tail = (last value).observation otherTail) :
    (view.bind next later).observation { tail with outputs := first.outputs ++ tail.outputs } =
      (view.bind other last).observation { otherTail with outputs := first.outputs ++ otherTail.outputs } := by
  dsimp only [observation]
  apply Prod.ext
  · have values := congrArg Prod.fst same
    exact values
  · change (view.bind next later).project (first.outputs ++ tail.outputs) =
      (view.bind other last).project (first.outputs ++ otherTail.outputs)
    rw [project_bind_return branch view returned, project_bind_return branch view returned]
    exact congrArg (view.project first.outputs ++ ·) (congrArg Prod.snd same)

/-- A branch after a shared raw prefix has a weakly matching branch when its returned
continuation compares at the prefix's exact raw context. Stopping prefixes match themselves.
Proof sketch: keep the prefix branch, match its tail and concatenate projected observations. -/
theorem Sql.View.observation_bind_branch {α β : Type} {program : Sql α}
    (view : View program) (state : ExecutionContext) (next other : α → Sql β)
    (later : ∀ value, View (next value)) (last : ∀ value, View (other value))
    (tails : ∀ beforeRun, program.Branch state.clock state.index state.connection beforeRun →
      ∀ value, beforeRun.value = some value → (later value).ObservationEquivAt (last value) (state.finish beforeRun))
    {result : SqlRun β} (branch : (program.bind next).Branch state.clock state.index state.connection result) :
    ∃ matched, (program.bind other).Branch state.clock state.index state.connection matched ∧
      (view.bind other last).observation matched = (view.bind next later).observation result := by
  obtain ⟨first, before, continuation⟩ := (Sql.branch_bind_iff program next _ _ _ result).mp branch
  cases returned : first.value with
  | none =>
    simp only [returned] at continuation
    subst result
    refine ⟨_, before.bind_stopped returned other, ?_⟩
    dsimp only [observation]
    apply Prod.ext
    · rfl
    · exact (project_bind_stopped before view returned other last).trans
        (project_bind_stopped before view returned next later).symm
  | some value =>
    simp only [returned] at continuation
    obtain ⟨tail, tailBranch, rfl⟩ := continuation
    obtain ⟨otherTail, otherBranch, equal⟩ := ((observationProfile_eq_iff.mp (tails first before value returned)).2 _).mp
      ⟨tail, tailBranch, rfl⟩
    exact ⟨_, before.bind_return returned other otherBranch,
      observation_bind_return_eq view before returned other next last later otherTail tail equal⟩

/-- After the same raw prefix and view, weakly equivalent continuations can replace
each other if every returning prefix branch reaches their raw comparison domain.
This rule does not replace a prefix using weak comparison. Proof sketch: preserve each
prefix branch and apply the continuation comparison at its exact reached inputs. -/
theorem Sql.View.ObservationEquivOn.bind_same {α β : Type} {program : Sql α}
    (view : View program) {next other : α → Sql β}
    {later : ∀ value, View (next value)} {last : ∀ value, View (other value)}
    {pre : ExecutionContext → Prop} {post : α → ExecutionContext → Prop}
    (tails : ∀ value, ObservationEquivOn (post value) (later value) (last value))
    (reaches : program.ReturnsIn pre post) :
    ObservationEquivOn pre (view.bind next later) (view.bind other last) := by
  intro state entry
  have forward beforeRun branch value returned := tails value _ (reaches state entry beforeRun branch value returned)
  apply observationProfile_eq_iff.mpr
  constructor
  · rw [Sql.runFrom_bind, Sql.runFrom_bind]
    let first := program.runFrom state.clock state.index state.connection
    have before : program.Branch state.clock state.index state.connection first := Sql.Branch.actual program _ _ _
    change (view.bind next later).observation (first.andThen _) =
      (view.bind other last).observation (first.andThen _)
    cases returned : first.value with
    | none =>
      simp only [SqlRun.andThen, returned]
      dsimp only [observation]
      apply Prod.ext
      · rfl
      · exact (project_bind_stopped before view returned next later).trans
          (project_bind_stopped before view returned other last).symm
    | some value =>
      simp only [SqlRun.andThen, returned]
      exact observation_bind_return_eq view before returned next other later last _ _
        (observationProfile_actual (forward first before value returned))
  · intro observed
    constructor
    · rintro ⟨result, branch, seen⟩
      obtain ⟨matched, permitted, equal⟩ := observation_bind_branch view state next other later last forward branch
      exact ⟨matched, permitted, equal.trans seen⟩
    · rintro ⟨result, branch, seen⟩
      obtain ⟨matched, permitted, equal⟩ := observation_bind_branch view state other next last later
        (fun beforeRun branch value returned => (forward beforeRun branch value returned).symm) branch
      exact ⟨matched, permitted, equal.trans seen⟩

end Belay.Sqlite
