import Belay.Sqlite.MigrationPatternFresh

set_option doc.verso true

namespace Belay.Sqlite.Migration

/-- A pure migration preserves every application at every supplied context and
predicate. It adds no step and returns immediately. Proof sketch: its continuation
and view reduce to the unchanged application's identity view. -/
theorem preserves_pure {μ α : Type} (value : μ) (application : Sql α) (pre : ExecutionContext → Prop) :
    PreservesOn (.pure value) pre application := by
  intro state _
  exact rfl

/-- A pure migration preserves every admitted read-only query in all valid databases
and complete fresh environments. Proof sketch: specialize pure preservation at each
initial context; no state or environment assumption is discarded. -/
theorem queryPreserves_pure {μ : Type} (value : μ) (query : Script) (pre : Database → Prop)
    (readOnly : query.isQuery = true) : QueryPreserves (.pure value) query pre readOnly := by
  intro db _ env _
  exact preserves_pure value (send query) (fun _ => True) (ExecutionContext.initial db env)

/-- A translation over a context predicate also holds over a stronger predicate,
with the same migration-success domain. Proof sketch: strengthen only the supplied
predicate; reuse success at the identical original context. -/
theorem TranslatesOn.restrict {μ α : Type} {migration : Sql μ} {original replacement : Sql α}
    {pre narrower : ExecutionContext → Prop} (same : TranslatesOn migration pre original replacement)
    (implies : ∀ state, narrower state → pre state) : TranslatesOn migration narrower original replacement := by
  intro state entry
  exact same state ⟨implies state entry.1, entry.2⟩

/-- Full commutation over a context predicate also holds over a stronger predicate,
without adding success of the moved migration. Proof sketch: strengthen only the
explicit precondition at the original context. -/
theorem CommutesAsOn.restrict {μ α : Type} {migration : Sql μ} {application replacement : Sql α}
    {pre narrower : ExecutionContext → Prop} (same : CommutesAsOn migration pre application replacement)
    (implies : ∀ state, narrower state → pre state) : CommutesAsOn migration narrower application replacement := by
  intro state entry
  exact same state ⟨implies state entry.1, entry.2⟩

/-- If the migration does not succeed at the original context, translation on its
success domain imposes no comparison there. Proof sketch: the domain includes the
contradicted success assumption. This is vacuity, not a success theorem. -/
theorem translatesAt_of_failure {μ α : Type} (migration : Sql μ) (pre : ExecutionContext → Prop)
    (original replacement : Sql α) (state : ExecutionContext)
    (failure : ¬ migration.SucceedsFrom state.clock state.index state.connection) :
    TranslatesAt migration pre original replacement state := fun entry => False.elim (failure entry.2)

/-- Original migration failure also makes the full commutation instance vacuous.
Failure only after moving the application does not satisfy this premise.
Proof sketch: the domain's original success contradicts the given failure. -/
theorem commutesAsAt_of_failure {μ α : Type} (migration : Sql μ) (pre : ExecutionContext → Prop)
    (application replacement : Sql α) (state : ExecutionContext)
    (failure : ¬ migration.SucceedsFrom state.clock state.index state.connection) :
    CommutesAsAt migration pre application replacement state := fun entry => False.elim (failure entry.2)

end Belay.Sqlite.Migration
