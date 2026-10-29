import Belay.Sqlite.Model.ResolveStatementFacts
import Belay.Sqlite.Model.Resolution.Resolve

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every context in execution mode, valid starting catalog and script that resolves: the catalog
after the script is valid under the limits of the profile of the context. Proof sketch: induction over
the script with {name}`resolveStatement_certificate`; the starting state has no saved catalog. -/
theorem resolve_valid (context : ResolveContext) (catalog after : Catalog) (script : List Syntax.Statement)
    (statements : List Resolved.Statement) (execution : context.mode = .execution)
    (valid : catalog.Valid context.profile.limits)
    (ok : resolve context catalog script = .resolved statements after) :
    after.Valid context.profile.limits := by
  have general : ∀ (script : List Syntax.Statement) index (state final : ResolveState) statements,
      state.Valid context.profile.limits → resolveFrom context index state script = .ok (statements, final) →
      final.Valid context.profile.limits := by
    intro script
    induction script with
    | nil => intro index state final statements valid ok; cases ok; exact valid
    | cons statement rest ih =>
      intro index state final statements valid ok
      simp only [resolveFrom, bind, Except.bind] at ok
      split at ok <;> try contradiction
      rename_i first hfirst
      split at ok <;> try contradiction
      rename_i later hlater
      cases ok
      exact ih _ _ _ _ ((resolveStatement_certificate _ _ _ _ _ hfirst).valid execution valid) hlater
  unfold resolve at ok
  split at ok <;> try contradiction
  rename_i result hresult
  cases ok
  exact (general _ _ _ _ _ ⟨valid, by simp [ResolveState.initial]⟩ hresult).1

end Belay.Sqlite.Model
