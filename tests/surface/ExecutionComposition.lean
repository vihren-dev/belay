import ExecutionProofs
import Belay.Sqlite.ExecutionEquivalenceBind

set_option doc.verso true

namespace ExecutionExamples
open Belay.Sqlite

/-- Both congruence directions accept arbitrary result-dependent continuations. -/
theorem two_sided_bind {α β : Type} {first second : Sql α} {left right : α → Sql β}
    (same : first ≈ second) (tails : ∀ value, left value ≈ right value) :
    first.bind left ≈ second.bind right := Sql.Equiv.bind same tails

/-- Replacing only the prefix keeps the continuation's full observations. -/
theorem replace_prefix {α β : Type} {first second : Sql α} (same : first ≈ second)
    (next : α → Sql β) : first.bind next ≈ second.bind next := Sql.Equiv.bind_right same next

/-- Replacing only result-dependent continuations keeps the prefix's reached contexts. -/
theorem replace_continuations {α β : Type} (program : Sql α) {left right : α → Sql β}
    (same : ∀ value, left value ≈ right value) : program.bind left ≈ program.bind right :=
  Sql.Equiv.bind_left program same

/-- Sent scripts compose through the same strong equivalence. -/
theorem replace_appended_scripts {first second left right : Script}
    (same : send first ≈ send second) (tails : send left ≈ send right) :
    send (first ++ left) ≈ send (second ++ right) := send_append_equiv same tails

/-- The concrete write reaches the value-dependent domain needed to replace its continuation. -/
theorem restricted_write : Sql.EquivOn (fun state => state = initial)
    (writeOne.bind fun count => .pure (count + 1)) (writeOne.bind fun _ => .pure 2) := by
  apply Sql.EquivOn.bind (post := fun count final =>
    count = 1 ∧ (final.connection.state.database.rowsAt 0).length = 3)
    (Sql.Equiv.on (Sql.Equiv.refl writeOne) _)
  · intro count state reached
    rw [reached.1]
    exact Sql.EquivAt.refl _ _
  · apply Sql.returnsIn_of_check
    intro state entry
    exact writeOne_spec state entry

/-- Removing the reached-domain premise makes even a universal restricted bind rule false.
An empty continuation domain makes its comparison vacuous, while pure still reaches a context. -/
theorem reaches_is_essential : ¬ (∀ (first second : Sql Unit) (left right : Unit → Sql Nat),
    Sql.EquivOn (fun _ => True) first second →
    (∀ value, Sql.EquivOn (fun _ => False) (left value) (right value)) →
    Sql.EquivOn (fun _ => True) (first.bind left) (second.bind right)) := by
  intro rule
  have falseSame := rule (.pure ()) (.pure ()) (fun _ => .pure 1) (fun _ => .pure 2)
    (Sql.Equiv.on (Sql.Equiv.refl (.pure ())) _) (fun _ _ impossible => impossible.elim)
    initial True.intro
  have returned := congrArg SqlRun.value falseSame.actual
  contradiction

/-- A transported fresh success claim still quantifies every complete environment. -/
theorem success_transport {α : Type} {first second : Sql α} (same : first ≈ second)
    (predicate : Database → Prop) (success : Succeeds first predicate) : Succeeds second predicate :=
  (Sql.Equiv.succeeds_iff same predicate).mp success

#print axioms two_sided_bind
#print axioms replace_prefix
#print axioms replace_continuations
#print axioms replace_appended_scripts
#print axioms restricted_write
#print axioms reaches_is_essential
#print axioms success_transport
#print axioms sqlSetoid
#print axioms Sql.EquivAt.refl
#print axioms Sql.EquivAt.symm
#print axioms Sql.EquivAt.trans
#print axioms Sql.EquivOn.bind
#print axioms Sql.Equiv.bind
#print axioms Sql.Equiv.bind_left
#print axioms Sql.Equiv.bind_right
#print axioms Sql.Equiv.map
#print axioms send_append_equiv
#print axioms Sql.returnsIn_of_check
end ExecutionExamples
