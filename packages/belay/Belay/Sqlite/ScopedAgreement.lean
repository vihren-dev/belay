import Belay.Sqlite.ExecutionBranchLaws
import Belay.Sqlite.ExecutionContext

set_option doc.verso true

/-! Scoped agreement of two programs (ADR 0017, S8). Two programs that start at two related
contexts agree under a context relation when their actual runs agree and each branch of one
has a matching branch of the other. A run agrees with another run when the returned value
and the outputs are equal and the finished contexts are related. The relation names which parts
of the two contexts may differ, for example a counter that only the second program changes.
Nothing else is hidden: both programs run normally from their own clock, index and connection. -/

namespace Belay.Sqlite

/-- Two runs of programs with the same value type agree under a relation, when the first run
started at one context and the second at another. In order:

* both runs return the same optional value, so both stop or both return the same value;
* both runs have the same outputs, including a stopping output and every error;
* the contexts that the runs reach (with the raw index and the full connection) are related.

The relation is the only place where a difference of the reached contexts is allowed. -/
def RunsAgree {α : Type} (related : ExecutionContext → ExecutionContext → Prop)
    (first second : ExecutionContext) (one other : SqlRun α) : Prop :=
  one.value = other.value ∧ one.outputs = other.outputs ∧ related (first.finish one) (second.finish other)

/-- Every branch of the left program from the first context has a branch of the right program from
the second context such that the two runs agree ({name}`RunsAgree`). A branch can be an
actual, raw, concrete, errored or stopped outcome; none is skipped. The reverse direction is a
separate claim. -/
def BranchesCovered {α : Type} (related : ExecutionContext → ExecutionContext → Prop)
    (left right : Sql α) (first second : ExecutionContext) : Prop :=
  ∀ one, left.Branch first.clock first.index first.connection one →
    ∃ other, right.Branch second.clock second.index second.connection other ∧
      RunsAgree related first second one other

/-- The scoped agreement of two programs at two contexts under a relation. All of these hold.

* The actual runs agree: equal value, equal outputs and related reached contexts.
* Every branch of the left program from the first context is matched by a branch of the right
  program from the second context, with equal value, equal outputs and related reached contexts.
* Every branch of the right program is matched by a branch of the left program in the same way.

The claim says nothing about the reached contexts beyond the relation. In particular it does not
say that the reached contexts are equal. -/
structure Sql.ScopedAt {α : Type} (related : ExecutionContext → ExecutionContext → Prop)
    (left right : Sql α) (first second : ExecutionContext) : Prop where
  /-- The actual runs of the two programs agree. -/
  actual : RunsAgree related first second
    (left.runFrom first.clock first.index first.connection)
    (right.runFrom second.clock second.index second.connection)
  /-- Each branch of the left program has an agreeing branch of the right program. -/
  forward : BranchesCovered related left right first second
  /-- Each branch of the right program has an agreeing branch of the left program. The relation
  reads its arguments in the same order: the left context first. -/
  backward : BranchesCovered (fun later earlier => related earlier later) right left second first

/-- Scoped agreement at every pair of contexts that the relation relates. A pair outside the
relation requires nothing. Use a relation that holds at the start of the application and that the
programs keep. -/
def Sql.ScopedOn {α : Type} (related : ExecutionContext → ExecutionContext → Prop)
    (left right : Sql α) : Prop :=
  ∀ first second, related first second → Sql.ScopedAt related left right first second

/-- Scoped agreement is symmetric when the relation is turned around. Proof sketch: the two runs
agree in the reverse direction because the equalities are symmetric, and the forward and backward
claims change places. -/
theorem Sql.ScopedAt.flip {α : Type} {related : ExecutionContext → ExecutionContext → Prop}
    {left right : Sql α} {first second : ExecutionContext}
    (agrees : Sql.ScopedAt related left right first second) :
    Sql.ScopedAt (fun later earlier => related earlier later) right left second first :=
  ⟨⟨agrees.actual.1.symm, agrees.actual.2.1.symm, agrees.actual.2.2⟩, agrees.backward, agrees.forward⟩

/-- A program agrees with itself under any relation that holds for the start contexts' own
finished contexts, for example the equality of the contexts. This is the case in which a program is
its own replacement. Proof sketch: every run matches itself and the contexts are the same. -/
theorem Sql.ScopedAt.refl {α : Type} (program : Sql α) (context : ExecutionContext)
    (related : ExecutionContext → ExecutionContext → Prop)
    (closed : ∀ result : SqlRun α, related (context.finish result) (context.finish result)) :
    Sql.ScopedAt related program program context context :=
  ⟨⟨rfl, rfl, closed _⟩, fun one branch => ⟨one, branch, rfl, rfl, closed one⟩,
    fun one branch => ⟨one, branch, rfl, rfl, closed one⟩⟩

/-- A pure program agrees with a pure program of the same value under every relation that holds
for the start contexts. A pure program sends nothing, so it keeps the contexts. Proof sketch: the
only branch of a pure program is its sole run, which changes neither connection nor outputs. -/
theorem Sql.ScopedOn.pure {α : Type} (related : ExecutionContext → ExecutionContext → Prop)
    (value : α) : Sql.ScopedOn related (.pure value) (.pure value) := by
  intro first second entry
  have kept : ∀ context : ExecutionContext, context.finish
      ({ outputs := [], connection := context.connection, value := some value } : SqlRun α) = context := by
    intro context; simp [ExecutionContext.finish]
  have branch : ∀ context : ExecutionContext, ∀ result : SqlRun α,
      (Sql.pure value : Sql α).Branch context.clock context.index context.connection result →
        result = { outputs := [], connection := context.connection, value := some value } := by
    intro context result b
    exact (Sql.branch_pure_iff value _ _ _ result).mp b
  have agree : RunsAgree related first second
      ({ outputs := [], connection := first.connection, value := some value } : SqlRun α)
      { outputs := [], connection := second.connection, value := some value } :=
    ⟨rfl, rfl, by rw [kept, kept]; exact entry⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [Sql.runFrom] using agree
  · intro one b
    rw [branch first one b]
    exact ⟨_, .pure value _ _ _, agree⟩
  · intro one b
    rw [branch second one b]
    exact ⟨_, .pure value _ _ _, rfl, rfl, by rw [kept, kept]; exact entry⟩

/-- A program agrees with itself under a relation, when related contexts have the same clock, the same
statement index and the same connection, and the relation keeps this after any run. Only the other
parts of the contexts, for example the earlier outputs, can differ. Proof sketch: the two runs and
all branches start from the same clock, index and connection, so they are the same runs; the finished
contexts are related by the closure premise. -/
theorem Sql.ScopedOn.same_program {α : Type} (related : ExecutionContext → ExecutionContext → Prop)
    (program : Sql α)
    (execution : ∀ first second, related first second →
      first.clock = second.clock ∧ first.index = second.index ∧ first.connection = second.connection)
    (closed : ∀ first second (result : SqlRun α), related first second →
      related (first.finish result) (second.finish result)) : Sql.ScopedOn related program program := by
  intro first second entry
  obtain ⟨clock, index, connection⟩ := execution first second entry
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [clock, index, connection]
  · rw [clock, index, connection]
  · rw [clock, index, connection]
    exact closed _ _ _ entry
  · intro one branch
    exact ⟨one, by rw [← clock, ← index, ← connection]; exact branch, rfl, rfl, closed _ _ _ entry⟩
  · intro one branch
    exact ⟨one, by rw [clock, index, connection]; exact branch, rfl, rfl, closed _ _ _ entry⟩

end Belay.Sqlite
