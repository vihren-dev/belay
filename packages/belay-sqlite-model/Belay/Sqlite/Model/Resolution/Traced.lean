import Belay.Sqlite.Model.Resolution.NameTraceTypes
import Belay.Sqlite.Model.Resolution.TracedAttr

set_option doc.verso true

/-! The monad that threads the name trace through the resolver. A traced computation is an
{lit}`Except` result together with the occurrences that it recorded. The trace survives an
error, so a failed resolution still says which names it decided before it failed. Every resolver
function that decides a name is the projection ({lit}`Traced.drop`) of its traced form, so the
trace and the resolved statement agree by construction. -/

namespace Belay.Sqlite.Model

/-- A computation that fails with {lit}`ε` or gives an {lit}`α`, and records name occurrences on
the way. After a failure the trace holds the occurrences recorded before it. -/
structure Traced (ε α : Type) where
  /-- The outcome without the trace: the function that a resolver function projects to. -/
  drop : Except ε α
  /-- The occurrences recorded, in the order in which the resolver reached them. -/
  trace : NameTrace

/-- Prefix the path of an occurrence. -/
def NameOccurrence.under (prefix_ : List Nat) (occurrence : NameOccurrence) : NameOccurrence :=
  { occurrence with path := prefix_ ++ occurrence.path }

namespace Traced
variable {ε ε' α β : Type}

/-- A success with no occurrence. -/
def ok (value : α) : Traced ε α := ⟨.ok value, []⟩

/-- A failure with no occurrence. -/
def error (issue : ε) : Traced ε α := ⟨.error issue, []⟩

/-- Run a computation, then the one that its value selects, keeping both traces; after a failure
the second does not run. -/
protected def bind (first : Traced ε α) (next : α → Traced ε β) : Traced ε β :=
  match first.drop with
  | .error issue => ⟨.error issue, first.trace⟩
  | .ok value => ⟨(next value).drop, first.trace ++ (next value).trace⟩

/-- The traced computations form a monad: {lit}`bind` joins the traces in order, and a failure ends the
computation with the trace so far. -/
instance : Monad (Traced ε) where
  pure := Traced.ok
  bind := Traced.bind

/-- Recover from a failure; the trace of the failed computation stays. -/
protected def tryCatch (first : Traced ε α) (handler : ε → Traced ε α) : Traced ε α :=
  match first.drop with
  | .error issue => ⟨(handler issue).drop, first.trace ++ (handler issue).trace⟩
  | .ok value => ⟨.ok value, first.trace⟩

/-- A traced computation can throw an issue and recover from it; the trace of the failed part stays. -/
instance : MonadExceptOf ε (Traced ε) where
  throw := Traced.error
  tryCatch := Traced.tryCatch

/-- A computation without a trace, such as a lookup that decides no name. -/
def lift (result : Except ε α) : Traced ε α := ⟨result, []⟩

/-- A result without a trace can run inside a traced computation. -/
instance : MonadLift (Except ε) (Traced ε) := ⟨Traced.lift⟩

/-- Record one occurrence. -/
def record (occurrence : NameOccurrence) : Traced ε Unit := ⟨.ok (), [occurrence]⟩

/-- Record several occurrences, in order. -/
def recordAll (occurrences : NameTrace) : Traced ε Unit := ⟨.ok (), occurrences⟩

/-- Change the type of the failure; the trace stays. -/
def mapError (change : ε → ε') (computation : Traced ε α) : Traced ε' α :=
  ⟨computation.drop.mapError change, computation.trace⟩

/-- Change the value; the trace stays. -/
protected def map (change : α → β) (computation : Traced ε α) : Traced ε β :=
  ⟨computation.drop.map change, computation.trace⟩

/-- Failures that carry node paths, so that a computation of a child can be moved below the
node of its parent. -/
class Underable (ε : Type) where
  /-- Prefix the paths of the failure. -/
  under : List Nat → ε → ε

/-- Move a computation below a child node: the paths of its failure and of its occurrences get the
prefix of the child. -/
def under [Underable ε] (prefix_ : List Nat) (computation : Traced ε α) : Traced ε α :=
  ⟨computation.drop.mapError (Underable.under prefix_), computation.trace.map (NameOccurrence.under prefix_)⟩

/-- Move the occurrences below a child node and keep the failure as it is. -/
def underTrace (prefix_ : List Nat) (computation : Traced ε α) : Traced ε α :=
  ⟨computation.drop, computation.trace.map (NameOccurrence.under prefix_)⟩

attribute [traced_drop] Traced.bind Traced.tryCatch

/-- For every value: the projection of a success is the success. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem drop_ok (value : α) : (Traced.ok value : Traced ε α).drop = .ok value := rfl
/-- For every issue: the projection of a failure is the failure. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem drop_error (issue : ε) : (Traced.error issue : Traced ε α).drop = .error issue := rfl
/-- For every result: lifting a result into the traced monad does not change it. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem drop_lift (result : Except ε α) : (Traced.lift result).drop = result := rfl
/-- For every result: lifting an {lit}`Except` result with {lit}`liftM` into the traced monad does not
change it. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem drop_liftM (result : Except ε α) : (liftM result : Traced ε α).drop = result := rfl
/-- For every occurrence: recording it gives a success with no value. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem drop_record (occurrence : NameOccurrence) :
    (Traced.record occurrence : Traced ε Unit).drop = .ok () := rfl
/-- For every list of occurrences: recording them gives a success with no value. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem drop_recordAll (occurrences : NameTrace) :
    (Traced.recordAll occurrences : Traced ε Unit).drop = .ok () := rfl
/-- For every change of issues and computation: the projection of the changed computation is the
changed projection. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem drop_mapError (change : ε → ε') (computation : Traced ε α) :
    (computation.mapError change).drop = computation.drop.mapError change := rfl
/-- For every change of values and computation: the projection of the changed computation is the
changed projection. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem drop_map (change : α → β) (computation : Traced ε α) :
    (computation.map change).drop = computation.drop.map change := rfl
/-- For every prefix and computation: moving a computation below a node moves the paths of its
issue and leaves its value. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem drop_under [Underable ε] (prefix_ : List Nat) (computation : Traced ε α) :
    (computation.under prefix_).drop = computation.drop.mapError (Underable.under prefix_) := rfl
/-- For every prefix and computation: moving only the occurrences below a node leaves the
projection unchanged. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem drop_underTrace (prefix_ : List Nat) (computation : Traced ε α) :
    (computation.underTrace prefix_).drop = computation.drop := rfl

/-- For every computation and continuation: the projection of a sequence is the sequence of the
projections, so tracing changes no result. Proof sketch: unfold the definitions, push the projection through the monad with {lit}`traced_drop`, and split on the cases of the arm. -/
@[traced_drop] theorem drop_bind (first : Traced ε α) (next : α → Traced ε β) :
    (first >>= next).drop = first.drop >>= fun value => (next value).drop := by
  show (Traced.bind first next).drop = _
  unfold Traced.bind
  cases first.drop <;> rfl

/-- For every issue: the projection of a thrown issue is the thrown issue. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem drop_throw (issue : ε) : (throw issue : Traced ε α).drop = .error issue := rfl

/-- For every condition: the projection of a choice is the choice of the projections. Proof sketch: unfold the definitions, push the projection through the monad with {lit}`traced_drop`, and split on the cases of the arm. -/
@[traced_drop] theorem drop_ite (condition : Prop) [Decidable condition] (yes no : Traced ε α) :
    (if condition then yes else no).drop = if condition then yes.drop else no.drop := by
  split <;> rfl

/-- For every condition: the projection of a dependent choice is the choice of the projections. Proof sketch: unfold the definitions, push the projection through the monad with {lit}`traced_drop`, and split on the cases of the arm. -/
@[traced_drop] theorem drop_dite (condition : Prop) [Decidable condition] (yes : condition → Traced ε α)
    (no : ¬condition → Traced ε α) :
    (if h : condition then yes h else no h).drop = if h : condition then (yes h).drop else (no h).drop := by
  split <;> rfl

/-- For every value: the projection of {lit}`pure` is {lit}`pure`. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem drop_pure (value : α) : (pure value : Traced ε α).drop = pure value := rfl

/-- For every value and continuation: a success followed by a continuation is the continuation. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem except_ok_bind (value : α) (next : α → Except ε β) :
    (Except.ok value >>= next) = next value := rfl

/-- For every issue and continuation: a failure followed by a continuation is the failure. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem except_error_bind (issue : ε) (next : α → Except ε β) :
    (Except.error issue >>= next) = Except.error issue := rfl

/-- For every issue: {lit}`throw` in {lit}`Except` is {lit}`Except.error`. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem except_throw (issue : ε) : (throw issue : Except ε α) = Except.error issue := rfl

/-- For every value and change: changing the failure of a success leaves it. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem except_mapError_ok (change : ε → ε') (value : α) :
    Except.mapError change (Except.ok value) = Except.ok value := rfl

/-- For every issue and change: changing the failure of a failure changes the issue. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem except_mapError_error (change : ε → ε') (issue : ε) :
    Except.mapError change (Except.error issue : Except ε α) = Except.error (change issue) := rfl

/-- For every value: {lit}`pure` in {lit}`Except` is {lit}`Except.ok`. Proof sketch: both sides are equal by definition. -/
@[traced_drop] theorem except_pure (value : α) : (pure value : Except ε α) = Except.ok value := rfl

end Traced
end Belay.Sqlite.Model
