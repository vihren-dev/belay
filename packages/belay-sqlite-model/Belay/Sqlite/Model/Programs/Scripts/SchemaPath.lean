import Belay.Sqlite.Model.Programs.Scripts.SchemaPathStep
import Belay.Sqlite.Model.Schema.Dispatch.Resolve

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The resolution state after the first {lit}`count` statements of a resolved script,
starting at {lit}`initial`. Use zero for the state before the script. A count greater
than the script length gives the final state. -/
def ResolveState.atPrefix (initial : ResolveState) (resolved : List Resolved.Statement)
    (count : Nat) : ResolveState :=
  (resolved.take count).foldl ResolveState.after initial

/-- For every script that resolves, folding the transitions of its resolved statements
from the initial resolution state gives the final state, and there is one resolved statement per input. Proof sketch: the resolver
certificate identifies the first transition, and induction covers the remaining script. -/
theorem resolveFrom_final {context : ResolveContext} {index : Nat} {initial final : ResolveState}
    {script : List Syntax.Statement} {resolved : List Resolved.Statement}
    (found : resolveFrom context index initial script = .ok (resolved, final)) :
    resolved.foldl ResolveState.after initial = final ∧ resolved.length = script.length := by
  induction script generalizing index initial resolved with
  | nil => cases found; exact ⟨rfl, rfl⟩
  | cons head rest ih =>
    simp only [resolveFrom, bind, Except.bind] at found
    split at found
    · contradiction
    · rename_i first next firstOk
      split at found
      · contradiction
      · rename_i tail tailOk
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj found)
        rw [List.foldl_cons, ← (resolveStatement_certificate context _ _ _ _ firstOk).after]
        obtain ⟨finalEq, len⟩ := ih tailOk
        exact ⟨finalEq, congrArg Nat.succ len⟩

/-- For every script that resolves and every position containing a statement, the
resolved list contains a statement there. Resolving the original statement at that
prefix gives that resolved statement and the state of the next prefix. Proof sketch:
induct on the script and position together. The resolver certificate gives the first
transition and the induction hypothesis gives the remaining ones. -/
theorem resolveFrom_atPrefix {context : ResolveContext} {index : Nat} {initial final : ResolveState}
    {script : List Syntax.Statement} {resolved : List Resolved.Statement} {n : Nat} {stmt : Syntax.Statement}
    (found : resolveFrom context index initial script = .ok (resolved, final))
    (atStmt : script[n]? = some stmt) :
    ∃ r, resolved[n]? = some r ∧ resolveStatement context (initial.atPrefix resolved n) stmt =
      .ok (r, initial.atPrefix resolved (n + 1)) := by
  induction script generalizing index initial resolved n with
  | nil => simp at atStmt
  | cons head rest ih =>
    simp only [resolveFrom, bind, Except.bind] at found
    split at found
    · contradiction
    · rename_i first next firstOk
      split at found
      · contradiction
      · rename_i tail tailOk
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj found)
        have nextEq := (resolveStatement_certificate context _ _ _ _ firstOk).after
        subst next
        cases n with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at atStmt
          subst stmt
          exact ⟨first, rfl, firstOk⟩
        | succ n =>
          obtain ⟨r, atR, resolveR⟩ := ih tailOk (by simpa using atStmt)
          exact ⟨r, atR, resolveR⟩

end Belay.Sqlite.Model
