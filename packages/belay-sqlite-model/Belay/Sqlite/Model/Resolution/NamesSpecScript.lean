import Belay.Sqlite.Model.Resolution.NamesSpec

set_option doc.verso true

/-! The script-level unique-names rule of resolution: a successful resolution of a script keeps the
folded names of the catalog unique, by induction with {lit}`resolveStatement_namesUnique`. -/

namespace Belay.Sqlite.Model

/-- For every context, starting catalog and script with a successful resolution: if
the starting catalog has unique folded names, so does the resulting catalog.
Proof sketch: induction on the script with {name}`resolveStatement_namesUnique`. -/
theorem resolve_namesUnique (context : ResolveContext) (catalog after : Catalog)
    (script : List Syntax.Statement) (statements : List Resolved.Statement)
    (unique : catalog.NamesUnique)
    (ok : resolve context catalog script = .resolved statements after) : after.NamesUnique := by
  have general : ∀ (script : List Syntax.Statement) index (state final : ResolveState) statements,
      state.NamesUnique → resolveFrom context index state script = .ok (statements, final) →
      final.NamesUnique := by
    intro script
    induction script with
    | nil => intro index state final statements unique ok; cases ok; exact unique
    | cons statement rest ih =>
      intro index state final statements unique ok
      simp only [resolveFrom, bind, Except.bind] at ok
      split at ok <;> try contradiction
      rename_i first hfirst
      split at ok <;> try contradiction
      rename_i later hlater
      cases ok
      exact ih _ _ _ _ (resolveStatement_namesUnique _ _ _ _ _ unique hfirst) hlater
  unfold resolve at ok
  split at ok <;> try contradiction
  rename_i result hresult
  cases ok
  exact (general _ _ _ _ _ ⟨unique, by simp [ResolveState.initial]⟩ hresult).1

end Belay.Sqlite.Model
