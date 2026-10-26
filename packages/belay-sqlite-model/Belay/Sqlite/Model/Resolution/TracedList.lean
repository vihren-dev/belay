import Belay.Sqlite.Model.Resolution.Traced
import Belay.Sqlite.Model.Resolution.Assignments

set_option doc.verso true

/-! Traced forms of the list helpers of the resolver: resolve a list in order and stop at the first
issue, keeping the occurrences of every item that ran, including the failing one. -/

namespace Belay.Sqlite.Model

/-- The traced form of {name}`resolveAllFrom`: resolve the items in order from a starting position,
and stop at the first issue; the trace holds the occurrences of the items up to the failing one. -/
def resolveAllFromTraced (resolveOne : Nat → α → Traced ε β) (start : Nat) :
    List α → Traced ε (List β)
  | [] => pure []
  | item :: rest => do
    let value ← resolveOne start item
    let values ← resolveAllFromTraced resolveOne (start + 1) rest
    return value :: values

/-- The traced form of {name}`resolveAll`: resolve a list in order from position zero. -/
def resolveAllTraced (resolveOne : Nat → α → Traced ε β) (items : List α) : Traced ε (List β) :=
  resolveAllFromTraced resolveOne 0 items

/-- For every item function, start and list: the projection of {name}`resolveAllFromTraced` is
{name}`resolveAllFrom` of the projected item function. Proof sketch: induction on the list. -/
@[traced_drop] theorem Traced.drop_resolveAllFromTraced (resolveOne : Nat → α → Traced ε β) (start : Nat)
    (items : List α) :
    (resolveAllFromTraced resolveOne start items).drop = resolveAllFrom (fun position item => (resolveOne position item).drop) start items := by
  induction items generalizing start with
  | nil => rfl
  | cons item rest ih =>
    simp only [resolveAllFromTraced, resolveAllFrom, Traced.drop_bind, Traced.drop_pure, ih]

/-- For every item function and list: the projection of {name}`resolveAllTraced` is
{name}`resolveAll` of the projected item function. Proof sketch: unfold the definitions and push the projection through the monad with {lit}`traced_drop`. -/
@[traced_drop] theorem Traced.drop_resolveAllTraced (resolveOne : Nat → α → Traced ε β) (items : List α) :
    (resolveAllTraced resolveOne items).drop = resolveAll (fun position item => (resolveOne position item).drop) items :=
  Traced.drop_resolveAllFromTraced resolveOne 0 items

/-- Keep the occurrences of a computation only when it fails. A name decided by an earlier pass
that a later pass records again keeps its record in the later pass; the earlier pass shows its
names only when it is the one that fails. -/
def Traced.keepOnFailure (computation : Traced ε α) : Traced ε α :=
  ⟨computation.drop, match computation.drop with
    | .ok _ => []
    | .error _ => computation.trace⟩

/-- For every computation: keeping its occurrences only on failure does not change the result. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem Traced.drop_keepOnFailure (computation : Traced ε α) :
    computation.keepOnFailure.drop = computation.drop := rfl

end Belay.Sqlite.Model
