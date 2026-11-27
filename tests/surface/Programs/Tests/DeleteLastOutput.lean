import SelectContextCases

set_option doc.verso true
set_option sql.check false

namespace DeleteLastOutput
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open scoped Belay.Sqlite.LastOutput
open SelectContextCases (bigScript deleteScript)
open SelectJoinCases (shop)

/-- The equivalent read on the starting database. -/
def referenceScript : Script := sql r"SELECT customer_id, amount FROM orders WHERE customer_id IS NOT NULL AND amount > 5"

/-- For every shop database, deleting orders without a customer and then reading big
orders gives the same last output as filtering the initial orders. Proof sketch: the compiler
produces identical scan data, so the comparison closes directly. -/
theorem delete_last : deleteScript; bigScript ~ referenceScript on shop := by sql_run

/-- The compiler itself produces the same normalized plan on both sides. Proof sketch: reduce
the two successful compiler results and compare their data by reflexivity. -/
example : ((((deleteScript ++ bigScript).compileScan? shop).get (by rfl)).val) =
    ((referenceScript.compileScan? shop).get (by rfl)).val := rfl

#print axioms delete_last

/-- An overflowing ABS records an error before execution continues. -/
private def overflow := sql r"SELECT abs(-9223372036854775808)"

/-- A final query with a fixed output after the earlier error. -/
private def seven := sql r"SELECT 7"

example : (shop.run (send (overflow ++ seven))).outputs = [.error 1, .rows [[.integer 7]]] := by decide +kernel

example : overflow; seven ~ seven on shop := by
  intro db schema env complete
  apply observationProfile_of_singletons
  · exact fun run => Sql.branch_iff_actual _ _ _ _ run (by rfl)
  · exact fun run => Sql.branch_iff_actual _ _ _ _ run (by rfl)
  · rfl

example : ¬ (seven; overflow ~ seven on shop) := by
  intro same
  let env : Env := { Env.newConnection with clock := some fun _ => 0 }
  have actual := observationProfile_actual (same shop rfl env ⟨rfl, rfl, rfl, rfl⟩)
  change some (Output.error 1) = some (.rows [[.integer 7]]) at actual
  cases actual

example : (referenceScript ~ deleteScript; bigScript on shop) := by
  intro db schema env complete
  exact (delete_last db schema env complete).symm

end DeleteLastOutput
