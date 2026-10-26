import Belay.Sqlite.ScopedAgreement
import Belay.Sqlite.ProgramBindLaws
import Belay.Sqlite.ExecutionBind

set_option doc.verso true

/-! Scoped agreement across a bind (ADR 0017, S8). A prefix that agrees with its replacement under a
relation, and continuations that agree at every pair of related contexts, give agreeing binds. The
continuation can read the value that the prefix returned, so later calls can depend on earlier
results. The relation is the only link between the contexts that the prefixes reach. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- Two runs that agree, and continuations whose runs from the reached contexts agree, give runs of
the composed programs that agree. A pair of runs without a value is composed as a stopped run. Proof
sketch: split on the prefix value. Without a value both compositions keep the prefix runs. With a
value both continuations run from the finished contexts, and the finished context of the composed
run is the finished context of the continuation from the finished context of the prefix
({name}`ExecutionContext.finish_append`). -/
theorem RunsAgree.andThen {α β : Type} {related : ExecutionContext → ExecutionContext → Prop}
    {first second : ExecutionContext} {one other : SqlRun α}
    (agree : RunsAgree related first second one other)
    {next following : α → Connection → SqlRun β}
    (tails : ∀ value, one.value = some value →
      RunsAgree related (first.finish one) (second.finish other)
        (next value one.connection) (following value other.connection)) :
    RunsAgree related first second (one.andThen next) (other.andThen following) := by
  obtain ⟨sameValue, sameOutputs, reached⟩ := agree
  unfold SqlRun.andThen
  cases returned : one.value with
  | none =>
    rw [← sameValue, returned]
    exact ⟨rfl, sameOutputs, reached⟩
  | some value =>
    rw [← sameValue, returned]
    obtain ⟨laterValue, laterOutputs, laterReached⟩ := tails value returned
    refine ⟨laterValue, by simp [sameOutputs, laterOutputs], ?_⟩
    rw [← ExecutionContext.finish_append, ← ExecutionContext.finish_append] at laterReached
    simpa [sameOutputs] using laterReached

/-- Branch coverage composes over a bind, in one direction. Assume that every branch of the left
prefix from the first context has an agreeing branch of the right prefix from the second context
({name}`BranchesCovered`), and that for every returned value and every pair of related contexts, every
branch of the left continuation has an agreeing branch of the right continuation. Then every branch of
the left bind has an agreeing branch of the right bind. The other direction is a separate use of this
theorem with the relation turned around. The contexts of the continuation are exactly the pairs that a
matched prefix branch reaches. Proof sketch: split a branch of the left bind into a prefix branch and a
continuation branch ({name}`Sql.branch_bind_iff`), match the prefix branch, and match the continuation
branch from the pair of reached contexts. A prefix branch without a value skips the continuation on
both sides. -/
theorem BranchesCovered.bind {α β : Type} {related : ExecutionContext → ExecutionContext → Prop}
    {left right : Sql α} {next following : α → Sql β} {first second : ExecutionContext}
    (prefixes : BranchesCovered related left right first second)
    (tails : ∀ value (one other : ExecutionContext), related one other →
      BranchesCovered related (next value) (following value) one other) :
    BranchesCovered related (left.bind next) (right.bind following) first second := by
  intro result branch
  obtain ⟨prefixRun, prefixBranch, split⟩ := (Sql.branch_bind_iff left next _ _ _ result).mp branch
  obtain ⟨other, otherBranch, sameValue, sameOutputs, reached⟩ := prefixes prefixRun prefixBranch
  cases returned : prefixRun.value with
  | none =>
    simp only [returned] at split
    subst split
    have stopped : other.value = none := sameValue.symm.trans returned
    refine ⟨{ other with value := none }, ?_, rfl, sameOutputs, reached⟩
    refine (Sql.branch_bind_iff right following _ _ _ _).mpr ⟨other, otherBranch, ?_⟩
    simp [stopped]
  | some value =>
    simp only [returned] at split
    obtain ⟨last, lastBranch, rfl⟩ := split
    have sameReturned : other.value = some value := sameValue.symm.trans returned
    obtain ⟨lastOther, lastOtherBranch, lastValue, lastOutputs, lastReached⟩ :=
      tails value _ _ reached last lastBranch
    refine ⟨{ lastOther with outputs := other.outputs ++ lastOther.outputs }, ?_,
      lastValue, by simp [sameOutputs, lastOutputs], ?_⟩
    · refine (Sql.branch_bind_iff right following _ _ _ _).mpr ⟨other, otherBranch, ?_⟩
      simp only [sameReturned]
      exact ⟨lastOther, lastOtherBranch, rfl⟩
    · rw [← ExecutionContext.finish_append, ← ExecutionContext.finish_append] at lastReached
      simpa [sameOutputs] using lastReached

/-- Scoped agreement composes over a bind. If the prefixes agree under the relation at every pair
of related contexts, and each pair of continuations for the same returned value agrees under the
relation at every pair of related contexts, then the composed programs agree under the relation. The
reached contexts of the prefixes are related by the agreement of the prefixes, so no property of the
reached contexts is assumed. Proof sketch: {name}`RunsAgree.andThen` for the actual runs,
{name}`BranchesCovered.bind` for the branches of each direction, and the flipped relation for the
backward direction. -/
theorem Sql.ScopedOn.bind {α β : Type} {related : ExecutionContext → ExecutionContext → Prop}
    {left right : Sql α} {next following : α → Sql β}
    (prefixes : Sql.ScopedOn related left right)
    (tails : ∀ value, Sql.ScopedOn related (next value) (following value)) :
    Sql.ScopedOn related (left.bind next) (right.bind following) := by
  intro first second entry
  have head := prefixes first second entry
  refine ⟨?_, BranchesCovered.bind head.forward fun value one other r =>
      (tails value one other r).forward, ?_⟩
  · rw [Sql.runFrom_bind, Sql.runFrom_bind]
    refine RunsAgree.andThen head.actual fun value returned => ?_
    exact (tails value _ _ head.actual.2.2).actual
  · exact BranchesCovered.bind head.backward fun value one other r =>
      (tails value other one r).backward

end Belay.Sqlite
