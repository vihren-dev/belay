import Belay.Sqlite.Queries.Evaluation.Values
import Belay.Sqlite.Frontend.Embedding.SqlDocBindings

set_option doc.verso true

/-! The values of the parameters of a checked SQL documentation block. A block binds its
parameters in one of two ways. With named bindings, each parameter name is a header argument,
and the shared parameter plan in file mode decides the numbers. A {lit}`$name` is an argument like
the others and never a Lean variable, and {lit}`:a` and {lit}`?1` bind as in a {lit}`sql` term. With the explicit list, the header gives one list of values for each
statement and no name is needed. This module decides what is wrong with the inputs, as problems at the
SQL token or the header argument that the user can change. It does not elaborate Lean terms. -/

namespace Belay.Sqlite.SqlDoc

open Translation Belay.Sqlite

/-- The values of the statements for a plan: the value that {lit}`lookup` gives for the name of
each slot, or NULL for a slot that no parameter uses. -/
def planValues (plan : ParameterPlan) (lookup : String → Option Value) : List (List Value) :=
  plan.slots.map fun slots => slots.map fun
    | .null => Value.null
    | .source source => (lookup source.name).getD Value.null

/-- The problems of an explicit list of values: one list for each statement, and in each list one
value for each number from 1 to the largest number of the statement. A shorter list would bind
NULL by accident, and a longer one binds a number that the statement does not have, which
SQLite refuses. A number that no parameter uses takes any value, and NULL is the usual one. -/
def explicitProblems (statements : List (List Parameter)) (values : List (List Value)) : List Problem :=
  let header := Place.header "values"
  if statements.length != values.length then
    [{ place := header,
       message := s!"the list (values := ...) has {values.length} lists and the SQL has {statements.length} statements; give one list for each statement, and the empty list for a statement without parameters" }]
  else
    (statements.zip values).zipIdx.filterMap fun ((parameters, list), index) =>
      let largest := largestNumber parameters
      if list.length == largest then none
      else some { place := header,
                  message := s!"statement {index + 1} uses parameter numbers up to {largest}, and its list has {list.length} values; give one value for each number from 1 to {largest}, with NULL for a number that no parameter uses" }

end Belay.Sqlite.SqlDoc
