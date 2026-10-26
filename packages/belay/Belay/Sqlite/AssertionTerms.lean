import Belay.Sqlite.FreshRules
import Std.Do

set_option doc.verso true

/-!
Assertions on execution contexts for Std.Do triples about {lit}`Sql` programs. {lit}`holds` is the
default query assertion and {lit}`holdsInContext` the real-context one. {lit}`ifOk` and
{lit}`andOk` are the conditional and the total error policies as postconditions, and
{lit}`FreshEnsures` is the fresh-run claim of such a postcondition. Each equals the corresponding
{lit}`Sql.ifOk`, {lit}`Sql.andOk` or {lit}`FreshTriple` statement, so the notation adds no new
semantics.
-/

namespace Belay.Sqlite
open Std.Do Model

/-- A fact about an execution context, for the precondition and postcondition of an ordinary
Std.Do triple about {name}`Sql` programs. It is a function from the full context (clock, next
statement index, connection and trace) to a proposition. Use {lit}`⌜p⌝` for a plain Lean
proposition {lit}`p`. -/
abbrev ContextAssertion : Type := Assertion (.arg ExecutionContext .pure)

/-- {lit}`holds q`: the query {lit}`q` holds on the database that the context sees, with the
default observation of {name}`Holds` ({name}`Holds.reached`): no clock, unknown counters,
foreign keys off, no open transaction. The query must be one read-only statement, which the term
checks where it is written. It holds in an ordinary triple at every context, not only at a fresh
start; it states nothing about the actual clock, counters or settings. Use
{lit}`holdsInContext` for those. -/
def holds (script : Script) (query : script.isQuery = true := by check_query) : ContextAssertion :=
  fun context => ⌜Holds.reached script context query⌝

/-- {lit}`holdsInContext q`: the query {lit}`q` holds when it runs from the context
({name}`Holds.inContext`), with the actual clock at the next statement index, the actual
counters, settings and open transaction. Observing runs nothing, so the context keeps its index
and trace. A query that reads a clock or counter that the context lacks does not hold. -/
def holdsInContext (script : Script) (query : script.isQuery = true := by check_query) : ContextAssertion :=
  fun context => ⌜Holds.inContext script context query⌝

/-- The conditional postcondition for a program with a value: the assertion on the value and
final context is required only when the whole trace is error-free. The whole trace includes
the outputs before the program, so a modeled error in the prefix of an ordinary context removes
the obligation. Every branch must still remain modeled: an unmodeled stop is never excused.
Use {lit}`ifOk` when the assertion does not use the value. -/
def ifOkWith {α : Type} (post : α → ContextAssertion) : PostCond α (.arg ExecutionContext .pure) :=
  ⇓ value context => ⌜List.allOk context.outputs = true → (post value context).down⌝

/-- The total postcondition for a program with a value: the whole trace must be error-free and
the assertion must hold on the value and final context. The whole trace includes the outputs
before the program, so a modeled error in the prefix of an ordinary context makes it false.
Every branch must remain modeled. Use {lit}`andOk` when the assertion does not use the value. -/
def andOkWith {α : Type} (post : α → ContextAssertion) : PostCond α (.arg ExecutionContext .pure) :=
  ⇓ value context => ⌜List.allOk context.outputs = true ∧ (post value context).down⌝

/-- {lit}`ifOk P`: the conditional postcondition for the assertion {lit}`P`, which does not use
the returned value ({name}`ifOkWith`). For a fresh run, it requires {lit}`P` when no modeled SQL
error occurred. Use it when a failed statement is not a failure of the claim. -/
def ifOk {α : Type} (post : ContextAssertion) : PostCond α (.arg ExecutionContext .pure) :=
  ifOkWith fun _ => post

/-- {lit}`andOk P`: the total postcondition for the assertion {lit}`P`, which does not use the
returned value ({name}`andOkWith`). For a fresh run, it requires {lit}`P` and that no modeled SQL
error occurred. {lit}`andOk ⌜True⌝` states success. -/
def andOk {α : Type} (post : ContextAssertion) : PostCond α (.arg ExecutionContext .pure) :=
  andOkWith fun _ => post

/-- For every program, precondition and value-aware assertion, the ordinary triple with
{name}`ifOkWith` holds exactly when, at every context that satisfies the precondition,
{name}`Sql.ifOk` of the program holds for the assertion. Proof sketch: both sides unfold to the
same branch check. -/
theorem triple_ifOkWith_iff {α : Type} (program : Sql α) (pre : ContextAssertion)
    (post : α → ContextAssertion) :
    ⦃pre⦄ program ⦃ifOkWith post⦄ ↔
      ∀ context, (pre context).down → program.ifOk (fun value final => (post value final).down) context :=
  Iff.rfl

/-- For every program, precondition and value-aware assertion, the ordinary triple with
{name}`andOkWith` holds exactly when, at every context that satisfies the precondition,
{name}`Sql.andOk` of the program holds for the assertion. Proof sketch: both sides unfold to the
same branch check. -/
theorem triple_andOkWith_iff {α : Type} (program : Sql α) (pre : ContextAssertion)
    (post : α → ContextAssertion) :
    ⦃pre⦄ program ⦃andOkWith post⦄ ↔
      ∀ context, (pre context).down → program.andOk (fun value final => (post value final).down) context :=
  Iff.rfl

/-- The fresh-run triple of a standard postcondition: for each admitted database satisfying the
precondition and each complete environment, every branch from the initial context returns a
value and a reached context that satisfy the postcondition. The postcondition cannot name the
captured database or environment; use {name}`FreshTriple` for that. This is the form that
the {lit}`ensures` notation elaborates to. -/
def FreshEnsures {α : Type} (program : Sql α) (pre : Database → Prop)
    (post : PostCond α (.arg ExecutionContext .pure)) : Prop :=
  FreshTriple program pre fun _ _ value final => (post.1 value final).down

/-- For every program, precondition and value-aware assertion, a fresh run with
{name}`andOkWith` holds exactly when {name}`Sql.andOk` holds at every initial context of an
admitted database and a complete environment. Proof sketch: both sides unfold to the same check. -/
theorem FreshEnsures.andOkWith_iff {α : Type} (program : Sql α) (pre : Database → Prop)
    (post : α → ContextAssertion) : FreshEnsures program pre (andOkWith post) ↔
      ∀ db, pre db → ∀ env : Env, env.Complete →
        program.andOk (fun value final => (post value final).down) (ExecutionContext.initial db env) :=
  Iff.rfl

/-- For every program, precondition and value-aware assertion, a fresh run with
{name}`ifOkWith` holds exactly when {name}`Sql.ifOk` holds at every initial context of an
admitted database and a complete environment. The empty initial trace is error-free, so the
property is required whenever no error occurs in the run. Proof sketch: both sides unfold to the
same check. -/
theorem FreshEnsures.ifOkWith_iff {α : Type} (program : Sql α) (pre : Database → Prop)
    (post : α → ContextAssertion) : FreshEnsures program pre (ifOkWith post) ↔
      ∀ db, pre db → ∀ env : Env, env.Complete →
        program.ifOk (fun value final => (post value final).down) (ExecutionContext.initial db env) :=
  Iff.rfl

/-- For every script or program and database predicate, success over all admitted databases and
complete environments ({name}`Succeeds`) is the fresh run with {lit}`andOk ⌜True⌝`. Both sides
quantify the same databases and complete environments, and keep the raw and every concrete
{name}`Output.oneOf` continuation. Proof sketch: {name}`Sql.andOk_complete_iff`. -/
theorem Succeeds.iff_ensures {σ α : Type} [Runnable σ α] (program : σ) (pre : Database → Prop) :
    Succeeds program pre ↔ FreshEnsures (Runnable.toSql program) pre (andOk ⌜True⌝) :=
  (show Succeeds program pre ↔ Succeeds (Runnable.toSql program) pre from Iff.rfl).trans
    (Sql.andOk_complete_iff (Runnable.toSql program) pre).symm

end Belay.Sqlite
