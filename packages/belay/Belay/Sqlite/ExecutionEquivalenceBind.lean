import Belay.Sqlite.ExecutionEquivalenceLaws

set_option doc.verso true

namespace Belay.Sqlite

/-- Restricted equivalence composes when every returning prefix branch reaches the
continuation's comparison domain. Prefixes compare on the initial domain; continuations
compare on their value-dependent reached domains. Stopped prefixes skip both continuations
and require no reached-domain fact. Proof sketch: actual-run membership supplies the actual
continuation premise; the branch bind characterization splits every permitted outcome. -/
theorem Sql.EquivOn.bind {α β : Type} {first second : Sql α} {left right : α → Sql β}
    {pre : ExecutionContext → Prop} {post : α → ExecutionContext → Prop}
    (beforeSame : Sql.EquivOn pre first second)
    (tails : ∀ value, Sql.EquivOn (post value) (left value) (right value))
    (reaches : first.ReturnsIn pre post) :
    Sql.EquivOn pre (first.bind left) (second.bind right) := by
  intro state entry
  have same := beforeSame state entry
  constructor
  · rw [Sql.runFrom_bind, Sql.runFrom_bind, ← same.actual]
    unfold SqlRun.andThen
    split
    · rfl
    · rename_i value returned
      have reached := reaches state entry _ (Sql.Branch.actual first _ _ _) value returned
      have following := (tails value _ reached).actual
      dsimp only [ExecutionContext.finish] at following
      dsimp only
      rw [following]
  · intro result
    rw [Sql.branch_bind_iff, Sql.branch_bind_iff]
    constructor
    · rintro ⟨before, branch, later⟩
      refine ⟨before, (same.branches before).mp branch, ?_⟩
      cases returned : before.value with
      | none => simpa [returned] using later
      | some value =>
        simp only [returned] at later ⊢
        obtain ⟨after, continuation, rfl⟩ := later
        have following := tails value _ (reaches state entry before branch value returned)
        exact ⟨after, (following.branches after).mp continuation, rfl⟩
    · rintro ⟨before, branch, later⟩
      have original := (same.branches before).mpr branch
      refine ⟨before, original, ?_⟩
      cases returned : before.value with
      | none => simpa [returned] using later
      | some value =>
        simp only [returned] at later ⊢
        obtain ⟨after, continuation, rfl⟩ := later
        have following := tails value _ (reaches state entry before original value returned)
        exact ⟨after, (following.branches after).mpr continuation, rfl⟩

/-- Completely equivalent prefixes and pointwise completely equivalent continuations
give completely equivalent binds. Continuations may inspect their returned values.
Proof sketch: use the restricted rule with the domain that contains every context. -/
theorem Sql.Equiv.bind {α β : Type} {first second : Sql α} {left right : α → Sql β}
    (beforeSame : first ≈ second) (tails : ∀ value, left value ≈ right value) :
    first.bind left ≈ second.bind right := by
  have restricted := Sql.EquivOn.bind (Sql.Equiv.on beforeSame (fun _ => True))
    (fun value => Sql.Equiv.on (tails value) (fun _ => True)) (fun _ _ _ _ _ _ => True.intro)
  exact fun state => restricted state True.intro

/-- Replacing a completely equivalent prefix preserves bind with the same arbitrary
continuation. Proof sketch: the continuations are reflexively equivalent. -/
theorem Sql.Equiv.bind_right {α β : Type} {first second : Sql α}
    (same : first ≈ second) (next : α → Sql β) : first.bind next ≈ second.bind next :=
  Sql.Equiv.bind same (fun value => Sql.Equiv.refl (next value))

/-- Pointwise equivalent continuations may replace each other after any shared prefix.
Proof sketch: the prefix is reflexively equivalent and the bind rule retains reached contexts. -/
theorem Sql.Equiv.bind_left {α β : Type} (program : Sql α) {first second : α → Sql β}
    (same : ∀ value, first value ≈ second value) : program.bind first ≈ program.bind second :=
  Sql.Equiv.bind (Sql.Equiv.refl program) same

/-- Applying the same function to returned values preserves complete equivalence.
Stopped outcomes and all traces remain unchanged. Proof sketch: map is bind followed by pure. -/
theorem Sql.Equiv.map {α β : Type} {first second : Sql α} (same : first ≈ second)
    (function : α → β) : first.map function ≈ second.map function := by
  simpa only [Sql.bind_pure_map] using Sql.Equiv.bind_right same (fun value => Sql.pure (function value))

/-- Sending appended scripts respects complete equivalence of both sent parts.
The second part uses the first part's exact connection and next index; a stopped first
part skips it. Proof sketch: expand send-append, then use bind and map congruence. -/
theorem send_append_equiv {first second left right : Script}
    (beforeSame : send first ≈ send second) (suffix : send left ≈ send right) :
    send (first ++ left) ≈ send (second ++ right) := by
  rw [send_append, send_append]
  apply Sql.Equiv.bind beforeSame
  intro outputs
  change (send left).bind (fun after => .pure (outputs ++ after)) ≈
    (send right).bind (fun after => .pure (outputs ++ after))
  simpa only [Sql.bind_pure_map] using Sql.Equiv.map suffix (outputs ++ ·)

end Belay.Sqlite
