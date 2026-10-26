import ResolverDispatch
import Belay.Sqlite.Model.ResolveStatementApplied

set_option doc.verso true

namespace ProofBoundaries
open Belay.Sqlite.Model

/-- The original state-equation claim follows without catalog validity or
execution-mode assumptions. Proof sketch: project the unconditional field. -/
theorem after_original (context : ResolveContext) (state next : ResolveState)
    (statement : Syntax.Statement) (resolved : Resolved.Statement)
    (ok : resolveStatement context state statement = .ok (resolved, next)) :
    next = state.after resolved :=
  (resolve_certificate context state next statement resolved ok).after

/-- The original schema-link claim accepts any limits and needs no execution
mode or saved-catalog premise. Proof sketch: apply its conditional field. -/
theorem link_original {limits : Limits} (context : ResolveContext) (state next : ResolveState)
    (statement : Syntax.Statement) (resolved : Resolved.Statement)
    (valid : state.catalog.Valid limits)
    (ok : resolveStatement context state statement = .ok (resolved, next)) :
    resolved.SchemaLink state.catalog :=
  (resolve_certificate context state next statement resolved ok).link limits valid

/-- The original validity claim preserves current and saved catalogs under
the same limits and execution-mode premise. Proof sketch: apply its field. -/
theorem valid_original (context : ResolveContext) (state next : ResolveState)
    (statement : Syntax.Statement) (resolved : Resolved.Statement)
    (execution : context.mode = .execution) (valid : state.Valid context.profile.limits)
    (ok : resolveStatement context state statement = .ok (resolved, next)) :
    next.Valid context.profile.limits :=
  (resolve_certificate context state next statement resolved ok).valid execution valid

/-- The catalog-application consumer retains its original execution and validity
premises, including control statements. Proof sketch: ordinary statements use
the certificate; control statements leave the applied catalog unchanged. -/
theorem applied_original (context : ResolveContext) (state next : ResolveState)
    (statement : Syntax.Statement) (resolved : Resolved.Statement)
    (execution : context.mode = .execution) (valid : state.Valid context.profile.limits)
    (ok : resolveStatement context state statement = .ok (resolved, next)) :
    (resolved.applyCatalog state.catalog).Valid context.profile.limits := by
  cases control : resolved.isControl
  · have facts := resolve_certificate context state next statement resolved ok
    have kept := facts.valid execution valid
    rw [facts.after, state.after_of_isControl control] at kept
    exact kept.1
  · rw [Resolved.Statement.applyCatalog_of_control control]
    exact valid.1

end ProofBoundaries

#print axioms ProofBoundaries.after_original
#print axioms ProofBoundaries.link_original
#print axioms ProofBoundaries.valid_original
#print axioms ProofBoundaries.applied_original
