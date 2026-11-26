import Belay.Sqlite.Model.Queries.Evaluation.ExprEval

set_option doc.verso true

/-! Laws for proving that a function call can return a value on one row. -/

namespace Belay.Sqlite.Model.Resolved.CallSafety

/-- A call succeeds on these arguments if it returns any SQL value, including NULL. -/
def Succeeds (call : α → Except ε Value) (args : α) := ∃ v, call args = .ok v

/-- If the arguments have fault {name}`Fault.none`, the call returns a value, and the classifier
gives {name}`Fault.none` to each successful result, the joined fault is {name}`Fault.none`.
Substitute the successful result and the fault of its arguments into the join. -/
theorem callFault {call : α → Except ε Value} {args : α} {fault : Fault}
    (classify : Except ε Value → Fault) (ok : ∀ v, classify (.ok v) = .none)
    (inputs : fault = .none) (safe : Succeeds call args) :
    fault.join (classify (call args)) = .none := by
  obtain ⟨v, h⟩ := safe
  rw [h, ok, inputs]; rfl

/-- If the scalar function differs from {name}`ScalarFunction.iif`, its arguments have fault
{name}`Fault.none`, and {name}`ScalarFunction.apply` succeeds on their values, the fault of
the {name}`Expr.scalar` expression on this row is {name}`Fault.none`.
Proof sketch: each eager constructor uses the same fault calculation in the evaluator. -/
theorem scalarFault {f : ScalarFunction} {args : Arguments} {c : EvalContext} {r : List Value}
    (strict : f ≠ .iif) (inputs : (args.evaluate c r).2 = .none)
    (call : Succeeds f.apply (args.eval c r)) :
    ((Expr.scalar f args).evaluate c r).2 = .none := by
  have law := callFault Fault.ofFunction (fun _ => rfl) inputs call
  cases f <;> first | contradiction | exact law

/-- If the arguments have fault {name}`Fault.none` and {name}`Json.apply` succeeds on their
values paired with their subtype flags, the fault of {name}`Expr.json` is {name}`Fault.none`.
Apply the common call law with the JSON fault classifier. -/
theorem jsonFault {f : JsonFunction} {args : Arguments} {c : EvalContext} {r : List Value}
    (inputs : (args.evaluate c r).2 = .none)
    (call : Succeeds (Json.apply f) ((args.eval c r).zip (args.givesJson c r))) :
    ((Expr.json f args).evaluate c r).2 = .none := by
  exact callFault Fault.ofJson (fun _ => rfl) inputs call

/-- For every SQL value, {name}`Except.ok` of that value is a successful result. The value
itself witnesses the existential. -/
theorem succeedsOk (v : Value) : ∃ w, (Except.ok v : Except ε Value) = .ok w := ⟨v, rfl⟩

/-- If both operands have fault {name}`Fault.none`, the comparison has fault {name}`Fault.none`. Rewrite both sides of the fault join. -/
theorem compareFault {op aff x y coll c r}
    (a : (Expr.evaluate c r x).2 = .none) (b : (Expr.evaluate c r y).2 = .none) :
    ((Expr.compare op aff x y coll).evaluate c r).2 = .none := by
  change Fault.join _ _ = _
  rw [a, b]; rfl

/-- If the head and tail have fault {name}`Fault.none`, the argument list has fault {name}`Fault.none`. Substitute their faults in the join. -/
theorem consFault {x xs c r} (a : (Expr.evaluate c r x).2 = .none)
    (b : (Arguments.evaluate c r xs).2 = .none) :
    ((Arguments.cons x xs).evaluate c r).2 = .none := by
  change Fault.join _ _ = _
  rw [a, b]; rfl

/-- A fault-free expression passes the row check for a WHERE clause. Reduce the singleton
filter check and substitute the fault. -/
theorem filterSafe {e : Expr} {c r} (safe : (e.evaluate c r).2 = .none) :
    (some e).toList.any (·.mayFailOn c r) = false := by
  change (_ != Fault.none || false) = false
  rw [safe]; rfl

/-- If the arguments have fault {name}`Fault.none`, the date call has fault {name}`Fault.none`.
The evaluator returns the argument fault directly. -/
theorem dateFault {f args c r} (safe : (Arguments.evaluate c r args).2 = .none) :
    ((Expr.date f args).evaluate c r).2 = .none := safe

/-- An IIF call is safe when the condition and the tail are safe. Substitute both faults in the
evaluator's join, which softens the fault of the tail. -/
theorem iifFault {head tail c r} (a : (Expr.evaluate c r head).2 = .none)
    (b : (Arguments.evaluate c r tail).2 = .none) :
    ((Expr.scalar .iif (.cons head tail)).evaluate c r).2 = .none := by
  change Fault.join _ (Fault.soften _) = _
  rw [a, b]; rfl

end Belay.Sqlite.Model.Resolved.CallSafety
