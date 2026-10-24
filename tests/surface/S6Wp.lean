import Belay.Sqlite.ProgramSuccess
import Belay.Sqlite.ProgramBindLaws
import Belay.Sqlite.SqlTerm
import Belay.Sqlite.DbBang
import Std.Do
import Std.Tactic.Do

set_option doc.verso true

/-! A test-only predicate transformer over the existing SQL execution step. -/

namespace S6
open Belay.Sqlite Belay.Sqlite.Model Std.Do

/-- All inputs and observations that a later statement can use. The trace starts empty
for a fresh run; keep the other fields when composing programs. -/
structure Context where
  /-- The same statement-indexed clock is used throughout a run. -/
  clock : Option Clock
  /-- The index of the next statement. -/
  index : Nat
  /-- The full connection, including counters, settings and transaction snapshot. -/
  connection : Connection
  /-- Outputs already produced, including the actual raw alternative wrapper. -/
  outputs : List Output := []

/-- Advance after one existing model step; use the chosen output in this branch's trace. -/
def Context.next (state : Context) (output : Output) (connection : Connection) : Context :=
  { state with index := state.index + 1, connection, outputs := state.outputs ++ [output] }

/-- Every modeled branch reaches the postcondition. When {lit}`rejectErrors = true`,
each output must also be free of SQL errors. Pure programs check their value and current
context. An unmodeled step requires false. A continuing step checks its actual continuation
and, for {name}`Output.oneOf`, every listed concrete result; an empty list adds no requirement.
The model's existing step supplies every transition; this definition only adds proof obligations. -/
def check (rejectErrors : Bool) {α : Type} : Sql α → (α → Context → Prop) → Context → Prop
  | .pure value, post, state => post value state
  | .exec statement values rest, post, state =>
    match runScriptStep runContext state.clock state.index state.connection statement values with
    | .ended _ => False
    | .continued output connection =>
      (rejectErrors = true → output.isError = false) ∧
      check rejectErrors (rest output) post (state.next output connection) ∧
        match output with
        | .oneOf results => ∀ rows ∈ results,
          check rejectErrors (rest (.rows rows)) post (state.next (.rows rows) connection)
        | _ => True

/-- A finite program and decidable postcondition give a decidable check. This instance
allows kernel reduction of the concrete fixtures without an unchecked evaluation axiom. -/
noncomputable instance checkDecidable {α : Type} (reject : Bool) (program : Sql α)
    (post : α → Context → Prop) [∀ value state, Decidable (post value state)]
    (state : Context) : Decidable (check reject program post state) := by
  induction program generalizing state with
  | pure value => exact inferInstanceAs (Decidable (post value state))
  | exec statement values rest later =>
    unfold check
    split
    · exact isFalse id
    · rename_i output connection step
      haveI : ∀ output, Decidable (check reject (rest output) post (state.next output connection)) :=
        fun output => later output (state.next output connection)
      cases output <;> dsimp <;> infer_instance

/-- For either error policy and all programs, checking both postconditions together is
exactly checking each separately. Proof sketch: induction on the program; distribute
conjunction through the actual continuation and the universal alternative obligations. -/
theorem check_and {α : Type} (reject : Bool) (program : Sql α) :
    ∀ (first second : α → Context → Prop) (state : Context),
      check reject program (fun value state => first value state ∧ second value state) state ↔
      check reject program first state ∧ check reject program second state := by
  induction program with
  | pure value => intros; rfl
  | exec statement values rest later =>
    intro first second state
    simp only [check]
    split
    · simp
    · rename_i output connection step
      cases output <;> simp only [later, forall_and]
      all_goals simp [and_assoc, and_left_comm, and_comm]

/-- For either error policy and all programs, checking bind is checking the first program
with the continuation's check as its postcondition. The continuation receives the exact
context reached by that branch. Proof sketch: induction on the first program. -/
theorem check_bind {α β : Type} (reject : Bool) (program : Sql α) (next : α → Sql β) :
    ∀ (post : β → Context → Prop) (state : Context),
      check reject (program.bind next) post state =
        check reject program (fun value state => check reject (next value) post state) state := by
  induction program with
  | pure value => intros; rfl
  | exec statement values rest later =>
    intro post state
    simp only [Sql.bind, check]
    split
    · rfl
    · rename_i output connection step
      simp only [later]

/-- The isolated total-success transformer. SQL errors and model restrictions both fail its
precondition. Use the separate {name}`check` with false for a modeled conditional claim. -/
def transformer {α : Type} (program : Sql α) : PredTrans (.arg Context .pure) α where
  trans post state := ⟨check true program (fun value state => (post.1 value state).down) state⟩
  conjunctiveRaw first second := by
    apply SPred.bientails.of_eq
    ext state
    exact check_and true program (fun value state => (first.1 value state).down)
      (fun value state => (second.1 value state).down) state

/-- The test-only {name}`WPMonad` instance preserves pure and bind by {name}`check_bind`.
It becomes execution evidence only with the separate soundness theorem. -/
instance sqlWp : WPMonad Sql (.arg Context .pure) where
  wp := transformer
  wp_pure value := by ext post state; rfl
  wp_bind program next := by
    ext post state
    exact Iff.of_eq (check_bind true program next (fun value state => (post.1 value state).down) state)

/-- For every context, a pure value checks exactly the postcondition at that unchanged context. -/
theorem pure_rule {α : Type} (value : α) (post : α → Context → Prop) (state : Context) :
    check true (Sql.pure value) post state ↔ post value state := Iff.rfl

#print axioms check_and
#print axioms check_bind
#print axioms sqlWp
end S6
