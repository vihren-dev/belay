import Belay.Sqlite.Model.Schema.Dispatch.PossibleResultsExamples
import Belay.Sqlite.Model.Shared.Execution.Output

/-! The current model output does not record which order SQLite promises.

This file checks {lit}`possibleOn`, the function from which the model makes the output of a
query, through the example helper {lit}`possible`. On the guide's customers (bob before ada in
rowid order, both with priority 1), the model gives the same set of results, one list
{lit}`ada, bob`, for three queries. Native SQLite gives different lists for them (probe P0 in
{lit}`probes/probes.sql`): {lit}`bob, ada` for the first two and {lit}`ada, bob` for the third.
An application that reads the rows in order can see the difference, but an equality of model
outputs cannot. -/

namespace BagResults.CurrentOutputs

open Belay.Sqlite.Model PossibleResultsExamples

/-- {lit}`SELECT name FROM t`: no promised order. -/
def unordered : Option (List (List (List Value))) := possible (customers ++ [selectT [name "name"]])

/-- {lit}`SELECT name FROM t ORDER BY p`: one tie group of two rows. -/
def tied : Option (List (List (List Value))) :=
  possible (customers ++ [selectT [name "name"] [ascending "p"]])

/-- {lit}`SELECT name FROM t ORDER BY name`: a total order. -/
def byName : Option (List (List (List Value))) :=
  possible (customers ++ [selectT [name "name"] [ascending "name"]])

/-- The query with a total order has one result: the list ada, bob. -/
theorem byName_eq : byName = some [[[textValue "ada"], [textValue "bob"]]] := by decide +kernel

/-- The query without ORDER BY has the same set of results as the query with a total order. -/
theorem unordered_eq_byName : unordered = byName := by decide +kernel

/-- The query with one tie group has the same set of results as the query with a total order. -/
theorem tied_eq_byName : tied = byName := by decide +kernel

/-- So the outputs that the model makes from these results are equal too. -/
theorem outputs_equal :
    unordered.map Output.ofResults = byName.map Output.ofResults ∧
    tied.map Output.ofResults = byName.map Output.ofResults := by
  rw [unordered_eq_byName, tied_eq_byName]; exact ⟨rfl, rfl⟩

#print axioms byName_eq
#print axioms unordered_eq_byName
#print axioms tied_eq_byName
#print axioms outputs_equal

end BagResults.CurrentOutputs
