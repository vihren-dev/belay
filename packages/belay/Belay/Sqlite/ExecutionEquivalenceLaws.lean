import Belay.Sqlite.ExecutionEquivalence
import Belay.Sqlite.ExecutionFresh

set_option doc.verso true

namespace Belay.Sqlite

/-- Every program has its own complete observations at every fixed context.
Proof sketch: reflexivity of equality and each branch proposition. -/
theorem Sql.EquivAt.refl {α : Type} (program : Sql α) (state : ExecutionContext) :
    program.EquivAt program state := ⟨rfl, fun _ => Iff.rfl⟩

/-- Fixed-context equivalence is symmetric: both complete observations compare equally
in either direction. Proof sketch: reverse equality and each branch equivalence. -/
theorem Sql.EquivAt.symm {α : Type} {first second : Sql α} {state : ExecutionContext}
    (same : first.EquivAt second state) : second.EquivAt first state :=
  ⟨same.actual.symm, fun result => (same.branches result).symm⟩

/-- At one shared context, two complete equivalences compose transitively.
Proof sketch: compose actual equality and each branch equivalence. -/
theorem Sql.EquivAt.trans {α : Type} {first second third : Sql α} {state : ExecutionContext}
    (one : first.EquivAt second state) (two : second.EquivAt third state) :
    first.EquivAt third state :=
  ⟨one.actual.trans two.actual, fun result => (one.branches result).trans (two.branches result)⟩

/-- Every program is completely equivalent to itself at all contexts.
Proof sketch: apply fixed-context reflexivity at each context. -/
theorem Sql.Equiv.refl {α : Type} (program : Sql α) : program.Equiv program :=
  fun state => .refl program state

/-- Unrestricted complete equivalence is symmetric.
Proof sketch: reverse the fixed-context relation at each context. -/
theorem Sql.Equiv.symm {α : Type} {first second : Sql α}
    (same : first.Equiv second) : second.Equiv first := fun state => (same state).symm

/-- Unrestricted complete equivalence is transitive for all three programs.
Proof sketch: compose the fixed-context relations at each context. -/
theorem Sql.Equiv.trans {α : Type} {first second third : Sql α}
    (one : first.Equiv second) (two : second.Equiv third) : first.Equiv third :=
  fun state => (one state).trans (two state)

/-- Ordinary SQL equivalence compares complete actual and branch executions. The
standard notation {lean}`(Sql.pure 1 : Sql Nat) ≈ Sql.pure 1` uses this relation. -/
instance sqlSetoid {α : Type} : Setoid (Sql α) where
  r := Sql.Equiv
  iseqv := ⟨Sql.Equiv.refl, Sql.Equiv.symm, Sql.Equiv.trans⟩

/-- At a fixed context, equivalent programs check exactly the same arbitrary
postconditions, including their treatment of SQL errors and unmodeled stops.
Proof sketch: replace each complete branch using the branch-set equivalence. -/
theorem Sql.EquivAt.check_iff {α : Type} {first second : Sql α} {state : ExecutionContext}
    (same : first.EquivAt second state) (post : α → ExecutionContext → Prop) :
    first.check post state ↔ second.check post state := by
  constructor
  · intro checked result branch
    exact checked result ((same.branches result).mpr branch)
  · intro checked result branch
    exact checked result ((same.branches result).mp branch)

/-- Every unrestricted comparison can be used on any chosen domain. No fact is
required outside that domain. Proof sketch: specialize the unrestricted relation. -/
theorem Sql.Equiv.on {α : Type} {first second : Sql α} (same : first.Equiv second)
    (pre : ExecutionContext → Prop) : Sql.EquivOn pre first second := fun state _ => same state

/-- Total-correctness checking implies the weaker condition on returning branches.
Proof sketch: specialize the check at each returned value; stopped branches impose nothing. -/
theorem Sql.returnsIn_of_check {α : Type} {program : Sql α} {pre : ExecutionContext → Prop}
    {post : α → ExecutionContext → Prop}
    (checked : ∀ state, pre state → program.check post state) : program.ReturnsIn pre post := by
  intro state entry result branch value returned
  simpa [returned] using checked state entry result branch

/-- Complete equivalence gives equal standard predicate transformers for all postconditions.
Proof sketch: extensionality reduces the claim to fixed-context branch checking. -/
theorem Sql.Equiv.transformer {α : Type} {first second : Sql α} (same : first ≈ second) :
    first.transformer = second.transformer := by
  ext post state
  exact (same state).check_iff (fun value state => (post.1 value state).down)

/-- At one shared context, equivalent programs satisfy the same total-success properties.
Proof sketch: total success is a check with a trace conjunction. -/
theorem Sql.EquivAt.andOk_iff {α : Type} {first second : Sql α} {state : ExecutionContext}
    (same : first.EquivAt second state) (post : α → ExecutionContext → Prop) :
    first.andOk post state ↔ second.andOk post state := same.check_iff _

/-- At one shared context, equivalent programs satisfy the same conditional properties.
Both reject unmodeled branches even when a non-OK prefix removes the final-property obligation.
Proof sketch: conditional success is a check with a trace implication. -/
theorem Sql.EquivAt.ifOk_iff {α : Type} {first second : Sql α} {state : ExecutionContext}
    (same : first.EquivAt second state) (post : α → ExecutionContext → Prop) :
    first.ifOk post state ↔ second.ifOk post state := same.check_iff _

/-- Completely equivalent programs have the same fresh triples for every database predicate
and initial-database-dependent postcondition. Proof sketch: specialize checking at each
fresh context; the valid database and complete environment quantifiers remain unchanged. -/
theorem Sql.Equiv.fresh_iff {α : Type} {first second : Sql α} (same : first ≈ second)
    (pre : Database → Prop) (post : Database → Env → α → ExecutionContext → Prop) :
    FreshTriple first pre post ↔ FreshTriple second pre post := by
  constructor
  · intro checked db entry env complete
    exact ((same _).check_iff _).mp (checked db entry env complete)
  · intro checked db entry env complete
    exact ((same _).check_iff _).mpr (checked db entry env complete)

/-- Complete equivalence transports universal S4 success for every database predicate.
Both sides quantify complete environments and retain raw and concrete branches.
Proof sketch: transport fresh error-free triples through their exact success bridge. -/
theorem Sql.Equiv.succeeds_iff {α : Type} {first second : Sql α} (same : first ≈ second)
    (pre : Database → Prop) : Succeeds first pre ↔ Succeeds second pre := by
  rw [← FreshTriple.succeeds_iff, ← FreshTriple.succeeds_iff]
  exact Sql.Equiv.fresh_iff same pre _

end Belay.Sqlite
