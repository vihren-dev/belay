import Belay.Sqlite.Model.Schema.Dispatch.Examples
import Belay.Sqlite.Model.Queries.Evaluation.PossibleResultsExamples
import Belay.Sqlite.Model.Schema.Dispatch.SqlAdvance

set_option doc.verso true

/-! Examples of the results that SQLite may give (ADR 0018, D6), each checked by the kernel: the
guide's row order cases, a window that cuts one or two tie groups, the guide's pagination with
equal priorities, and {lit}`DISTINCT` and {lit}`GROUP BY` with {lit}`LIMIT`. -/

namespace Belay.Sqlite.Model.PossibleResultsExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- The results that SQLite may give for the last statement of the script, a query, after the
statements before it from the empty catalog. -/
def possible (script : List Syntax.Statement) : Option (List (List (List Value))) :=
  match (statements (migration [] script)).reverse with
  | (.query query subqueries) :: earlier =>
    let database := (runSql (bindValues earlier.reverse []) {}).database
    query.possibleOn 0 {} [] database subqueries
  | (.createTable ..) :: _ | (.createView ..) :: _ | (.createIndex ..) :: _ | (.createTrigger ..) :: _ | (.addColumn ..) :: _ | (.rewrite _) :: _ | (.dropColumn ..) :: _ | (.drop ..) :: _
  | .begin :: _ | .commit :: _ | .rollback :: _ | (.insert ..) :: _ | (.upsert ..) :: _ | (.insertSelect ..) :: _ | (.update ..) :: _
  | (.delete ..) :: _ | (.prepareError _) :: _ | (.setting ..) :: _ | [] => none

-- Without ORDER BY, one result in normal form: ada, bob.
example : possible (customers ++ [selectT [name "name"]]) = some [[[textValue "ada"], [textValue "bob"]]] := by
  decide +kernel
-- LIMIT 1 without ORDER BY: ada or bob.
example : possible (customers ++ [selectT [name "name"] [] (some 1)]) =
    some [[[textValue "bob"]], [[textValue "ada"]]] := by decide +kernel
-- When every choice gives the same rows, one result.
example : possible (customers ++ [selectT [.numeric "1"] [] (some 1)]) = some [[[.integer 1]]] := by decide +kernel
-- ORDER BY with ties: the tied rows in normal form.
example : possible (customers ++ [selectT [name "name"] [ascending "p"]]) =
    some [[[textValue "ada"], [textValue "bob"]]] := by decide +kernel

-- OFFSET 1 LIMIT 1 in one group of three: any of the three.
example : possible (jobs ++ [selectT [name "name"] [ascending "p"] (some 1) (some 1)]) =
    some [[[textValue "a"]], [[textValue "b"]], [[textValue "c"]]] := by decide +kernel
-- OFFSET 2 LIMIT 2 over two groups: one of the first group, then d.
example : possible (jobs ++ [selectT [name "name"] [ascending "p"] (some 2) (some 2)]) =
    some [[[textValue "a"], [textValue "d"]], [[textValue "b"], [textValue "d"]], [[textValue "c"], [textValue "d"]]] := by
  decide +kernel
-- Pagination: pages 0 and 1 of size 2 over ties may share a row, as page 1 may give a again.
#guard ((possible (jobs ++ [selectT [name "name"] [ascending "p"] (some 2) (some 2)])).getD []).any
  (·.contains [textValue "a"])
#guard ((possible (jobs ++ [selectT [name "name"] [ascending "p"] (some 2) none])).getD []).any
  (·.contains [textValue "a"])
-- DISTINCT and GROUP BY with LIMIT: the distinct priorities, or the groups, one of two.
example : possible (jobs ++ [selectT [name "p"] [] (some 1) none [] true]) = some [[[.integer 1]], [[.integer 2]]] := by
  decide +kernel
example : possible (jobs ++ [selectT [name "p"] [] (some 1) none [name "p"]]) = some [[[.integer 1]], [[.integer 2]]] := by
  decide +kernel

end Belay.Sqlite.Model.PossibleResultsExamples
