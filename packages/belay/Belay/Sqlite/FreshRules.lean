import Belay.Sqlite.ExecutionFresh
import Belay.Sqlite.ContextObservationLaws

set_option doc.verso true

/-!
Composition rules for fresh-run triples. The fresh entry (a captured database, a complete
environment, statement index zero and an empty trace) is fixed once at the outer program. Bind,
consequence and conjunction keep it, and an ordinary Std.Do triple about the continuation
serves as a rule inside a fresh run.
-/

namespace Belay.Sqlite
open Std.Do

/-- For every value, precondition and postcondition, a pure program satisfies a fresh triple
exactly when, at each admitted database and complete environment, the postcondition holds for
the value and the unchanged initial context. An unsatisfied precondition requires nothing.
Proof sketch: a pure program checks its postcondition at the starting context. -/
theorem FreshTriple.pure_iff {α : Type} (value : α) (pre : Database → Prop)
    (post : Database → Env → α → ExecutionContext → Prop) :
    FreshTriple (Sql.pure value) pre post ↔
      ∀ db, pre db → ∀ env : Env, env.Complete → post db env value (ExecutionContext.initial db env) := by
  simp only [FreshTriple, Sql.check_pure]

/-- For every program, continuation, precondition and postcondition, a bind satisfies a fresh
triple exactly when the first program does, with the continuation's branch check as its
postcondition. Each continuation starts at the exact reached context of one branch of the first
program and every permitted value. The captured database and environment stay those of the
outer entry. Proof sketch: unfold the fresh triple and apply {name}`Sql.check_bind`. -/
theorem FreshTriple.bind_iff {α β : Type} (program : Sql α) (next : α → Sql β) (pre : Database → Prop)
    (post : Database → Env → β → ExecutionContext → Prop) :
    FreshTriple (program.bind next) pre post ↔
      FreshTriple program pre (fun db env value final => (next value).check (post db env) final) := by
  simp only [FreshTriple, Sql.check_bind]

/-- A fresh triple stays true for a stronger precondition and a weaker postcondition, at the
same program. The stronger precondition must imply the original one for every database. The
weaker postcondition must follow from the original one for every database, environment, value
and context, not only for the ones that a run reaches. Proof sketch: monotonicity of the branch
check ({name}`Sql.check_mono`), after specializing to the stronger precondition. -/
theorem FreshTriple.mono {α : Type} {program : Sql α} {pre stronger : Database → Prop}
    {post weaker : Database → Env → α → ExecutionContext → Prop} (checked : FreshTriple program pre post)
    (entry : ∀ db, stronger db → pre db)
    (follows : ∀ db env value final, post db env value final → weaker db env value final) :
    FreshTriple program stronger weaker := fun db holds env complete =>
  Sql.check_mono (checked db (entry db holds) env complete) (follows db env)

/-- A conjunction of postconditions holds in a fresh triple exactly when both postconditions
do, each at the same admitted databases and complete environments. Proof sketch: the branch
check of a conjunction is the conjunction of the checks ({name}`Sql.check_and`). -/
theorem FreshTriple.and_iff {α : Type} (program : Sql α) (pre : Database → Prop)
    (first second : Database → Env → α → ExecutionContext → Prop) :
    FreshTriple program pre (fun db env value final => first db env value final ∧ second db env value final) ↔
      FreshTriple program pre first ∧ FreshTriple program pre second := by
  constructor
  · intro both
    exact ⟨fun db holds env complete => ((Sql.check_and program (first db env) (second db env) _).mp
        (both db holds env complete)).1, fun db holds env complete =>
        ((Sql.check_and program (first db env) (second db env) _).mp (both db holds env complete)).2⟩
  · rintro ⟨left, right⟩ db holds env complete
    exact (Sql.check_and program (first db env) (second db env) _).mpr
      ⟨left db holds env complete, right db holds env complete⟩

/-- An ordinary Std.Do triple for any context predicate gives a fresh triple when the initial
context of every admitted database and complete environment satisfies that predicate. The
ordinary triple keeps its arbitrary-context meaning, and the entry premise names the contexts
that the fresh run actually reaches. Example: the predicate can require an empty trace, or
{name}`Holds.reached` of a query. Proof sketch: specialize the ordinary triple at the initial
context. -/
theorem FreshTriple.of_triple {α : Type} {program : Sql α} {pre : Database → Prop}
    {entry : Database → Env → ExecutionContext → Prop} {post : Database → Env → α → ExecutionContext → Prop}
    (triple : ∀ db env, ⦃fun state : ExecutionContext => ⌜entry db env state⌝⦄
      program ⦃⇓ value state => ⌜post db env value state⌝⦄)
    (starts : ∀ db, pre db → ∀ env : Env, env.Complete → entry db env (ExecutionContext.initial db env)) :
    FreshTriple program pre post := fun db holds env complete =>
  triple db env _ (starts db holds env complete)

/-- Bind with an ordinary-context specification of the continuation. If the first program
satisfies a fresh triple whose postcondition is the middle predicate, and the continuation
satisfies an ordinary triple for each captured database, environment and value, then the
bind satisfies the fresh triple. The continuation's triple holds at every context that
satisfies the middle predicate, so the reached context of each branch is the premise.
Proof sketch: {name}`FreshTriple.bind_iff`, then apply the ordinary triple to each reached context. -/
theorem FreshTriple.bind_triple {α β : Type} {program : Sql α} {next : α → Sql β}
    {pre : Database → Prop} {middle : Database → Env → α → ExecutionContext → Prop}
    {post : Database → Env → β → ExecutionContext → Prop} (first : FreshTriple program pre middle)
    (continuation : ∀ db env value, ⦃fun state : ExecutionContext => ⌜middle db env value state⌝⦄
      next value ⦃⇓ result state => ⌜post db env result state⌝⦄) :
    FreshTriple (program.bind next) pre post :=
  (FreshTriple.bind_iff program next pre post).mpr
    (FreshTriple.mono first (fun _ holds => holds) (fun db env value final held =>
      continuation db env value final held))

end Belay.Sqlite
