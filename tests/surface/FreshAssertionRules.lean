import AssertionContexts
import Belay.Sqlite.AssertionTerms
import Belay.Sqlite.ExecutionWPLaws

set_option doc.verso true

/-! Fixtures for the composition rules of fresh-run triples: pure, bind, consequence,
conjunction, ordinary-triple continuations and a nested specification keep the captured database
and environment, and a fresh claim does not become a triple about every context. -/
set_option maxRecDepth 4096

namespace AssertionExamples
open Belay.Sqlite Belay.Sqlite.Model Std.Do

/-- Pure bind keeps the captured database and environment: the final context is the initial one. -/
theorem pure_bind_keeps_start :
    FreshTriple ((Sql.pure 1).bind fun value => Sql.pure (value + 1)) (fun _ => True)
      (fun db env value final => value = 2 ∧ final = ExecutionContext.initial db env) := by
  rw [FreshTriple.bind_iff]
  rw [FreshTriple.pure_iff]
  intro db _ env complete
  rw [Sql.check_pure]
  exact ⟨rfl, rfl⟩

/-- Consequence strengthens the database predicate and weakens the postcondition together. -/
theorem consequence_example :
    FreshTriple ((Sql.pure 1).bind fun value => Sql.pure (value + 1)) (fun db => db = sample)
      (fun _ _ value _ => value ≥ 1) :=
  pure_bind_keeps_start.mono (fun _ _ => True.intro) (fun _ _ _ _ both => by have := both.1; omega)

/-- Conjunction splits and joins fresh claims that share the same entry. -/
theorem conjunction_example :
    FreshTriple ((Sql.pure 1).bind fun value => Sql.pure (value + 1)) (fun _ => True)
      (fun db env value final => value = 2 ∧ final = ExecutionContext.initial db env) ↔
    FreshTriple ((Sql.pure 1).bind fun value => Sql.pure (value + 1)) (fun _ => True)
      (fun _ _ value _ => value = 2) ∧
    FreshTriple ((Sql.pure 1).bind fun value => Sql.pure (value + 1)) (fun _ => True)
      (fun db env _ final => final = ExecutionContext.initial db env) :=
  FreshTriple.and_iff _ _ _ _

/-- Two specified steps keep the captured database and environment: the postcondition of the second
step still names the original {lit}`db` and {lit}`env`. The first step enters from the exact initial
context, the second from the reached context, and the continuation is an ordinary triple. -/
theorem two_steps_keep_start (first : Sql Nat) (second : Nat → Sql Nat)
    (middle : Belay.Sqlite.Database → Env → Nat → ExecutionContext → Prop)
    (post : Belay.Sqlite.Database → Env → Nat → ExecutionContext → Prop)
    (firstSpec : ∀ db env, ⦃fun state : ExecutionContext => ⌜state = ExecutionContext.initial db env⌝⦄
      first ⦃⇓ value state => ⌜middle db env value state⌝⦄)
    (secondSpec : ∀ db env value, ⦃fun state : ExecutionContext => ⌜middle db env value state⌝⦄
      second value ⦃⇓ result state => ⌜post db env result state⌝⦄) :
    FreshTriple (first.bind second) (fun _ => True) post :=
  FreshTriple.bind_triple (FreshTriple.of_triple firstSpec (fun _ _ _ _ => rfl)) secondSpec

/-- A nested specification is an ordinary triple about a bind; the fresh rule accepts it as the
continuation without replacing the captured start. -/
theorem nested_continuation (first : Sql Nat) (second third : Nat → Sql Nat)
    (middle later : Belay.Sqlite.Database → Env → Nat → ExecutionContext → Prop)
    (post : Belay.Sqlite.Database → Env → Nat → ExecutionContext → Prop)
    (firstSpec : ∀ db env, ⦃fun state : ExecutionContext => ⌜state = ExecutionContext.initial db env⌝⦄
      first ⦃⇓ value state => ⌜middle db env value state⌝⦄)
    (secondSpec : ∀ db env value, ⦃fun state : ExecutionContext => ⌜middle db env value state⌝⦄
      second value ⦃⇓ result state => ⌜later db env result state⌝⦄)
    (thirdSpec : ∀ db env value, ⦃fun state : ExecutionContext => ⌜later db env value state⌝⦄
      third value ⦃⇓ result state => ⌜post db env result state⌝⦄) :
    FreshTriple (first.bind fun value => (second value).bind third) (fun _ => True) post :=
  two_steps_keep_start first _ middle post firstSpec fun db env value =>
    Std.Do.Triple.bind (second value) third (secondSpec db env value) (thirdSpec db env)

/-- A fresh claim does not become an ordinary-triple claim: with the same postcondition,
the ordinary triple from every context is refuted at a context with a later index. -/
theorem fresh_claim_is_not_reusable :
    FreshTriple (Sql.pure ()) (fun _ => True) (fun _ _ _ final => final.index = 0) ∧
    ¬ (⦃fun _ : ExecutionContext => ⌜True⌝⦄ Sql.pure () ⦃⇓ _ final => ⌜final.index = 0⌝⦄) := by
  refine ⟨fun db _ env _ => (Sql.check_pure _ _ _).mpr rfl, fun triple => ?_⟩
  have checked : (Sql.pure ()).check (fun _ final => final.index = 0) { initial with index := 4 } :=
    triple _ True.intro
  have impossible : (4 : Nat) = 0 := (Sql.check_pure _ _ _).mp checked
  contradiction

#print axioms pure_bind_keeps_start
#print axioms consequence_example
#print axioms conjunction_example
#print axioms two_steps_keep_start
#print axioms nested_continuation
#print axioms fresh_claim_is_not_reusable
end AssertionExamples
