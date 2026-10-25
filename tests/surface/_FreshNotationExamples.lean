import Belay
#eval IO.println "@@BEGIN"

/-! The fresh-run notation elaborates to the public primitives, accepts bound Lean values, and
checks the guard query at its own source position. -/

set_option doc.verso true

namespace FreshNotationExamples
open Belay.Sqlite Std.Do

/-- Unguarded notation is the fresh claim over every database. -/
theorem ensures_expansion : ((Sql.pure 1) ensures andOk ⌜True⌝) =
    FreshEnsures (Sql.pure 1) (fun _ => True) (andOk ⌜True⌝) := rfl

/-- Guarded notation uses the default {name}`Holds` of the guard on the starting database. -/
theorem guarded_expansion (value : Value) : ((Sql.pure 1) ensures andOk ⌜True⌝ where sql r"SELECT $value") =
    FreshEnsures (Sql.pure 1) (fun db => Holds (sql r"SELECT $value") db) (andOk ⌜True⌝) := rfl

/-- A script is a program through the existing {name}`Runnable` instance. -/
theorem script_expansion : ((sql r"SELECT 1") ensures ifOk ⌜True⌝) =
    FreshEnsures (send (sql r"SELECT 1")) (fun _ => True) (ifOk ⌜True⌝) := rfl

/-- The success notation equals the fresh form with the total policy and a true property. -/
theorem succeeds_is_total_ensures :
    ((Sql.pure 1) succeeds where sql r"SELECT 1") = ((Sql.pure 1) ensures andOk ⌜True⌝ where sql r"SELECT 1") :=
  propext (Succeeds.iff_ensures _ _)

/-- A value binder reaches the returned value in the postcondition. -/
example : ((Sql.pure 1) ensures (⇓ value => ⌜value = 1⌝)) :=
  fun _ _ _ _ => (Sql.check_pure _ _ _).mpr rfl

/-- Notation claims prove by their primitives. -/
example : ((Sql.pure 1) ensures andOk ⌜True⌝ where sql r"SELECT 1") :=
  (Succeeds.iff_ensures _ _).mp (Succeeds.pure _ _)

/--
@ +1:51...76
error: the script must be one read-only statement: a SELECT, or PRAGMA foreign_keys without a value; remove the other statements, or use Database.run
-/
#guard_msgs (positions := true) in
example : ((Sql.pure 1) ensures andOk ⌜True⌝ where sql r"SELECT 1; SELECT 2") := sorry

#print axioms ensures_expansion
#print axioms guarded_expansion
#print axioms script_expansion
#print axioms succeeds_is_total_ensures
end FreshNotationExamples
