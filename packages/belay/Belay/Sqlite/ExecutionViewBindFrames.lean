import Belay.Sqlite.ExecutionViewFrames
import Belay.Sqlite.ExecutionViewBind

set_option doc.verso true

namespace Belay.Sqlite

/-- Matching full prefix observations give matching stopped bind observations.
Neither continuation runs. Proof sketch: projection stops with the prefix, and
its connection and raw step count are unchanged. -/
theorem Sql.View.full_bind_stopped_eq {α β : Type} {first second : Sql α}
    (left : View first) (right : View second) (state : ExecutionContext)
    {one two : SqlRun α} (before : first.Branch state.clock state.index state.connection one)
    (after : second.Branch state.clock state.index state.connection two)
    (same : left.fullObservation state one = right.fullObservation state two)
    (stopped : one.value = none) (otherStopped : two.value = none)
    (next other : α → Sql β) (later : ∀ value, View (next value)) (last : ∀ value, View (other value)) :
    (left.bind next later).fullObservation state { one with value := none } =
      (right.bind other last).fullObservation state { two with value := none } := by
  obtain ⟨observed, connection, steps⟩ := (fullObservation_eq_iff _ _ _ _ _).mp same
  apply (fullObservation_eq_iff _ _ _ _ _).mpr
  refine ⟨?_, connection, steps⟩
  dsimp only [observation]
  apply Prod.ext
  · rfl
  · exact (project_bind_stopped before left stopped next later).trans
      ((congrArg Prod.snd observed).trans (project_bind_stopped after right otherStopped other last).symm)

/-- Equal full prefix observations and equal full tail observations give equal full
bind observations. Tail comparison uses the first prefix's raw reached context;
its accumulated raw trace cancels before the projected prefixes are assembled.
Proof sketch: concatenate projections and raw lengths, retaining tail values and connections. -/
theorem Sql.View.full_bind_return_eq {α β : Type} {first second : Sql α}
    (left : View first) (right : View second) (state : ExecutionContext)
    {one two : SqlRun α} (before : first.Branch state.clock state.index state.connection one)
    (after : second.Branch state.clock state.index state.connection two)
    (same : left.fullObservation state one = right.fullObservation state two)
    {value : α} (returned : one.value = some value) (otherReturned : two.value = some value)
    (next other : α → Sql β) (later : ∀ value, View (next value)) (last : ∀ value, View (other value))
    (tail otherTail : SqlRun β)
    (tailSame : (later value).fullObservation (state.finish one) tail =
      (last value).fullObservation (state.finish one) otherTail) :
    (left.bind next later).fullObservation state { tail with outputs := one.outputs ++ tail.outputs } =
      (right.bind other last).fullObservation state { otherTail with outputs := two.outputs ++ otherTail.outputs } := by
  obtain ⟨beforeRun, _, counts⟩ := (fullObservation_eq_iff _ _ _ _ _).mp same
  obtain ⟨suffix, connection, steps⟩ := (fullObservation_eq_iff _ _ _ _ _).mp tailSame
  apply (fullObservation_eq_iff _ _ _ _ _).mpr
  refine ⟨?_, connection, by simp only [List.length_append, counts, steps]⟩
  dsimp only [observation]
  apply Prod.ext
  · have values := congrArg Prod.fst suffix
    exact values
  · change (left.bind next later).project (one.outputs ++ tail.outputs) =
      (right.bind other last).project (two.outputs ++ otherTail.outputs)
    rw [project_bind_return before left returned, project_bind_return after right otherReturned]
    have beforeOutputs := congrArg Prod.snd beforeRun
    have afterOutputs := congrArg Prod.snd suffix
    change left.project one.outputs = right.project two.outputs at beforeOutputs
    change (later value).project tail.outputs = (last value).project otherTail.outputs at afterOutputs
    rw [beforeOutputs, afterOutputs]

/-- One full bind branch has a corresponding branch when prefixes compare fully and
all returning left prefixes admit the tail comparison at their exact raw reached context.
Stopped prefixes require no tail premise. Proof sketch: split the branch, match its prefix,
then match its tail at equal execution inputs and concatenate both observations. -/
theorem Sql.View.EquivAt.bind_branch {α β : Type} {first second : Sql α}
    {left : View first} {right : View second} {state : ExecutionContext}
    (same : left.EquivAt right state) (next other : α → Sql β)
    (later : ∀ value, View (next value)) (last : ∀ value, View (other value))
    (tails : ∀ beforeRun, first.Branch state.clock state.index state.connection beforeRun →
      ∀ value, beforeRun.value = some value → (later value).EquivAt (last value) (state.finish beforeRun))
    {result : SqlRun β} (branch : (first.bind next).Branch state.clock state.index state.connection result) :
    ∃ matched, (second.bind other).Branch state.clock state.index state.connection matched ∧
      (right.bind other last).fullObservation state matched = (left.bind next later).fullObservation state result := by
  obtain ⟨one, before, continuation⟩ := (Sql.branch_bind_iff first next _ _ _ result).mp branch
  obtain ⟨two, after, prefixSame⟩ := (same.branches _).mp ⟨one, before, rfl⟩
  have values := congrArg Prod.fst prefixSame
  obtain ⟨_, connections, steps⟩ := (fullObservation_eq_iff _ _ _ _ _).mp prefixSame
  cases returned : one.value with
  | none =>
    simp only [returned] at continuation
    subst result
    have stopped : two.value = none := values.trans returned
    exact ⟨_, after.bind_stopped stopped other,
      full_bind_stopped_eq right left state after before prefixSame stopped returned other next last later⟩
  | some value =>
    simp only [returned] at continuation
    obtain ⟨tail, tailBranch, rfl⟩ := continuation
    obtain ⟨otherTail, otherBranch, tailSame⟩ := ((tails one before value returned).branches _).mp
      ⟨tail, tailBranch, rfl⟩
    have otherReturned : two.value = some value := values.trans returned
    refine ⟨{ otherTail with outputs := two.outputs ++ otherTail.outputs },
      after.bind_return otherReturned other (last := otherTail) ?_, ?_⟩
    · simpa only [ExecutionContext.finish, connections, steps] using otherBranch
    · exact (full_bind_return_eq left right state before after prefixSame.symm returned otherReturned
        next other later last tail otherTail tailSame.symm).symm

end Belay.Sqlite
