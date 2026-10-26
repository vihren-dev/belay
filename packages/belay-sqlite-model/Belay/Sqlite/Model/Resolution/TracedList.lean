import Belay.Sqlite.Model.Resolution.Traced
import Belay.Sqlite.Model.Resolution.ResolveAll
import Belay.Sqlite.Model.Resolution.NameTraceSettled

set_option doc.verso true

/-! Helpers of the traced resolver that change the trace of a computation: keep it only on failure,
change its occurrences, or give each name once. -/

namespace Belay.Sqlite.Model

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

/-- Change every occurrence of a computation; the result stays. A resolver moves the occurrences of
a copy of a query back to the place of the written query this way. -/
def Traced.mapOccurrences (change : NameOccurrence → NameOccurrence) (computation : Traced ε α) : Traced ε α :=
  ⟨computation.drop, computation.trace.map change⟩

/-- For every change and computation: changing the occurrences does not change the result. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem Traced.drop_mapOccurrences (change : NameOccurrence → NameOccurrence)
    (computation : Traced ε α) : (computation.mapOccurrences change).drop = computation.drop := rfl

/-- Give each name of the occurrences once ({name}`NameTrace.settled`); the result stays. -/
def Traced.settle (computation : Traced ε α) : Traced ε α :=
  ⟨computation.drop, computation.trace.settled⟩

/-- For every computation: settling its occurrences does not change the result. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem Traced.drop_settle (computation : Traced ε α) : computation.settle.drop = computation.drop := rfl

/-- Run a traced step on each item in order and collect the values; the first failure ends the run and
the trace holds the occurrences of the items up to it. This is {lit}`List.mapM` with a traced step. -/
def Traced.mapAll (step : α → Traced ε β) : List α → Traced ε (List β)
  | [] => pure []
  | item :: rest => do
    let value ← step item
    let values ← Traced.mapAll step rest
    pure (value :: values)

/-- For every step function and list: the projection of {name}`Traced.mapAll` is the {lit}`mapM` of the
projected step. Proof sketch: induction on the list; push the projection through the monad. -/
@[traced_drop] theorem Traced.drop_mapAll (step : α → Traced ε β) (items : List α) :
    (Traced.mapAll step items).drop = items.mapM fun item => (step item).drop := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [Traced.mapAll, Traced.drop_bind, Traced.drop_pure, ih, List.mapM_cons]

/-- Run a traced step on each item in order, passing the state on; the first failure ends the run.
This is {lit}`List.foldlM` with a traced step. -/
def Traced.foldAll (step : β → α → Traced ε β) : β → List α → Traced ε β
  | state, [] => pure state
  | state, item :: rest => do
    let next ← step state item
    Traced.foldAll step next rest

/-- For every step function, start state and list: the projection of {name}`Traced.foldAll` is the
{lit}`foldlM` of the projected step. Proof sketch: induction on the list, generalizing the state; push
the projection through the monad. -/
@[traced_drop] theorem Traced.drop_foldAll (step : β → α → Traced ε β) (start : β) (items : List α) :
    (Traced.foldAll step start items).drop = items.foldlM (fun state item => (step state item).drop) start := by
  induction items generalizing start with
  | nil => rfl
  | cons item rest ih =>
    simp only [Traced.foldAll, Traced.drop_bind, ih, List.foldlM_cons]

end Belay.Sqlite.Model
