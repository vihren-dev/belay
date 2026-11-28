/-!
# Nondeterministic results

A query denotes the set of results that SQLite may give. `ND α` is that set, given as a
predicate on `α`. The monad structure composes the steps of a query plan: a later step may
depend on the result that an earlier step gave.
-/

namespace BagResults

/-- The results that a computation may give. SQLite may return any of them. -/
def ND (α : Type) : Type := α → Prop

/-- The monad of result sets. `pure a` permits only `a`. `m >>= f` permits each result of
`f a`, for each result `a` that `m` permits. -/
instance : Monad ND where
  pure a := fun b => b = a
  bind m f := fun b => ∃ a, m a ∧ f a b

namespace ND
variable {α β γ : Type}

/-- For all `a` and `b`: `pure a` permits `b` if and only if `b = a`. -/
@[simp] theorem pure_apply (a b : α) : (pure a : ND α) b ↔ b = a := Iff.rfl

/-- For all `m`, `f` and `b`: `m >>= f` permits `b` if and only if there is a result `a` of
`m` such that `f a` permits `b`. -/
@[simp] theorem bind_apply (m : ND α) (f : α → ND β) (b : β) :
    (m >>= f) b ↔ ∃ a, m a ∧ f a b := Iff.rfl

/-- For all `f`, `m` and `b`: `f <$> m` permits `b` if and only if `b = f a` for a result `a`
of `m`. -/
@[simp] theorem map_apply (f : α → β) (m : ND α) (b : β) :
    (f <$> m) b ↔ ∃ a, m a ∧ b = f a := Iff.rfl

/-- For all result sets `m₁` and `m₂`: if they permit the same results, then they are
equal. -/
theorem ext {m₁ m₂ : ND α} (same : ∀ a, m₁ a ↔ m₂ a) : m₁ = m₂ :=
  funext fun a => propext (same a)

/-- The result sets obey the monad laws. Each law is a short argument about `∃` and `=`. -/
instance : LawfulMonad ND := LawfulMonad.mk' ND
  (id_map := fun _ => ext fun b => ⟨fun ⟨_, h, e⟩ => e ▸ h, fun h => ⟨b, h, rfl⟩⟩)
  (pure_bind := fun x _ => ext fun _ => ⟨fun ⟨_, e, h⟩ => e ▸ h, fun h => ⟨x, rfl, h⟩⟩)
  (bind_assoc := fun _ _ _ => ext fun _ =>
    ⟨fun ⟨_, ⟨a, ma, fab⟩, gbc⟩ => ⟨a, ma, _, fab, gbc⟩,
     fun ⟨a, ma, b, fab, gbc⟩ => ⟨b, ⟨a, ma, fab⟩, gbc⟩⟩)

end ND

end BagResults
