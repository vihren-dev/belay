import Belay.Sqlite.ExecutionViewBindFrames

set_option doc.verso true

namespace Belay.Sqlite

/-- Full projected prefixes compose with full projected continuations when every
returning first-prefix branch reaches the continuation domain on its RAW context.
The right prefix may have a different hidden trace. Its equal execution inputs
permit transport of a proved tail comparison, without asserting the raw predicate
on that different trace. Stopped prefixes skip both tails. Proof sketch: use raw
ReturnsIn for actual and branch tails, match prefixes, and cancel prior traces. -/
theorem Sql.View.EquivOn.bind {α β : Type} {first second : Sql α}
    {left : View first} {right : View second} {next other : α → Sql β}
    {later : ∀ value, View (next value)} {last : ∀ value, View (other value)}
    {pre : ExecutionContext → Prop} {post : α → ExecutionContext → Prop}
    (prefixes : EquivOn pre left right)
    (tails : ∀ value, EquivOn (post value) (later value) (last value))
    (reaches : first.ReturnsIn pre post) : EquivOn pre (left.bind next later) (right.bind other last) := by
  intro state entry
  have same := prefixes state entry
  have forward beforeRun branch value returned := tails value _ (reaches state entry beforeRun branch value returned)
  have reverse : ∀ beforeRun, second.Branch state.clock state.index state.connection beforeRun →
      ∀ value, beforeRun.value = some value → (last value).EquivAt (later value) (state.finish beforeRun) := by
    intro two after value returned
    obtain ⟨one, before, equal⟩ := (same.branches _).mpr ⟨two, after, rfl⟩
    have values := congrArg Prod.fst equal
    obtain ⟨_, connections, steps⟩ := (fullObservation_eq_iff _ _ _ _ _).mp equal
    have compared := (forward one before value (values.trans returned)).symm.with_outputs (state.outputs ++ two.outputs)
    simpa only [ExecutionContext.finish, connections, steps] using compared
  constructor
  · rw [Sql.runFrom_bind, Sql.runFrom_bind]
    let one := first.runFrom state.clock state.index state.connection
    let two := second.runFrom state.clock state.index state.connection
    have before : first.Branch state.clock state.index state.connection one := Sql.Branch.actual first _ _ _
    have after : second.Branch state.clock state.index state.connection two := Sql.Branch.actual second _ _ _
    have equal : left.fullObservation state one = right.fullObservation state two := same.actual
    have values := congrArg Prod.fst equal
    obtain ⟨_, connections, steps⟩ := (fullObservation_eq_iff _ _ _ _ _).mp equal
    change (left.bind next later).fullObservation state (one.andThen _) =
      (right.bind other last).fullObservation state (two.andThen _)
    cases returned : one.value with
    | none =>
      have stopped : two.value = none := values.symm.trans returned
      simp only [SqlRun.andThen, returned, stopped]
      exact full_bind_stopped_eq left right state before after equal returned stopped next other later last
    | some value =>
      have otherReturned : two.value = some value := values.symm.trans returned
      simp only [SqlRun.andThen, returned, otherReturned]
      apply full_bind_return_eq left right state before after equal returned otherReturned next other later last
      change (later value).fullObservation (state.finish one)
          ((next value).runFrom state.clock (state.index + one.outputs.length) one.connection) =
        (last value).fullObservation (state.finish one)
          ((other value).runFrom state.clock (state.index + two.outputs.length) two.connection)
      simpa only [ExecutionContext.finish, connections, steps] using (forward one before value returned).actual
  · intro observed
    constructor
    · rintro ⟨result, branch, seen⟩
      obtain ⟨matched, permitted, equal⟩ := same.bind_branch next other later last forward branch
      exact ⟨matched, permitted, equal.trans seen⟩
    · rintro ⟨result, branch, seen⟩
      obtain ⟨matched, permitted, equal⟩ := same.symm.bind_branch other next last later reverse branch
      exact ⟨matched, permitted, equal.trans seen⟩

/-- Unrestricted full projected comparisons compose with value-dependent continuation
views at every context. Proof sketch: use the restricted rule with true domains.
Weak prefix comparison does not supply this law. -/
theorem Sql.View.Equiv.bind {α β : Type} {first second : Sql α}
    {left : View first} {right : View second} {next other : α → Sql β}
    {later : ∀ value, View (next value)} {last : ∀ value, View (other value)}
    (prefixes : Equiv left right) (tails : ∀ value, Equiv (later value) (last value)) :
    Equiv (left.bind next later) (right.bind other last) := by
  have composed := EquivOn.bind (pre := fun _ => True) (post := fun _ _ => True)
    (fun state _ => prefixes state) (fun value state _ => tails value state)
    (fun _ _ _ _ _ _ => True.intro)
  exact fun state => composed state True.intro

end Belay.Sqlite
