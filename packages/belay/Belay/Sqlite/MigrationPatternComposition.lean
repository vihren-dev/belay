import Belay.Sqlite.MigrationPatternQuiet

set_option doc.verso true

namespace Belay.Sqlite.Migration

/-- Observing an application after two quiet migrations equals observing it after
their combined quiet segment, with complete context retained. This statement covers
every failure and result-dependent migration branch. Proof sketch: associativity of
the original program and annotation concatenation give identical projections. -/
theorem after_compose {μ ν α : Type} (first : Sql μ) (second : Sql ν) (application : Sql α)
    (state : ExecutionContext) :
    (afterView (after first second) application).EquivAt
      ((Sql.View.quiet first).bind (fun _ => after second application) (fun _ => afterView second application)) state := by
  apply Sql.View.equiv_of_program_eq _ _ (Sql.bind_assoc first (fun _ => second) (fun _ => application)) state
  intro result _
  simp only [afterView, after, Sql.View.quiet, Sql.View.uniform_bind]
  exact Sql.View.project_bind_assoc _ _ _ _ _ result.outputs

/-- Query-style translations compose over two migrations when every returning first
migration branch preserves the second translation's explicit precondition on its raw
reached context. Success of the combined migration is tested at the original context;
the proved bind-success law supplies each component success. The programs may also be
used outside the read-only query helper. Proof sketch: apply the first translation,
replace its query tail using the second translation on every reached branch, and
reassociate the two quiet migration segments. -/
theorem TranslatesOn.compose {μ ν α : Type} {first : Sql μ} {second : Sql ν}
    {original middle replacement : Sql α} {pre intermediate : ExecutionContext → Prop}
    (one : TranslatesOn first pre original middle)
    (two : TranslatesOn second intermediate middle replacement)
    (reaches : first.ReturnsIn pre (fun _ => intermediate)) :
    TranslatesOn (after first second) pre original replacement := by
  have tails := Sql.View.ObservationEquivOn.bind_same (Sql.View.quiet first)
    (pre := Domain (after first second) pre) (post := fun _ => Domain second intermediate)
    (next := fun _ => middle) (other := fun _ => after second replacement)
    (later := fun _ => Sql.View.identity middle) (last := fun _ => afterView second replacement)
    (fun _ state entry => two state entry)
    (by
      intro state entry result branch value returned
      have successful := (Sql.succeedsFrom_bind_iff first (fun _ => second) _ _ _).mp entry.2
      exact ⟨reaches state entry.1 result branch value returned,
        successful.2 result branch value returned⟩)
  intro state entry
  have successful := (Sql.succeedsFrom_bind_iff first (fun _ => second) _ _ _).mp entry.2
  exact (one state ⟨entry.1, successful.1⟩).trans
    ((tails state entry).trans (Sql.View.EquivAt.observation (after_compose first second replacement state).symm))

/-- Preservation composes under the same raw reached-domain premise as translation.
The original success domain is that of the combined migration, not of a fresh reset.
Proof sketch: preservation is translation with the same application at both ends. -/
theorem PreservesOn.compose {μ ν α : Type} {first : Sql μ} {second : Sql ν}
    {application : Sql α} {pre intermediate : ExecutionContext → Prop}
    (one : PreservesOn first pre application) (two : PreservesOn second intermediate application)
    (reaches : first.ReturnsIn pre (fun _ => intermediate)) :
    PreservesOn (after first second) pre application := TranslatesOn.compose one two reaches

end Belay.Sqlite.Migration
