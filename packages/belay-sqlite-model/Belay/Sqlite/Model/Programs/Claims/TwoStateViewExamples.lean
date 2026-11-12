import Belay.Sqlite.Model.Programs.Claims.TwoStateExamples
import Belay.Sqlite.Model.Queries.Evaluation.TwoStateViewExamples

set_option doc.verso true

/-! Kernel checks of the observation of a query over two databases (ADR 0017, S6) for views, common
tables, subqueries, compounds, parameters, clocks, counters, errors and refusals.
{lit}`TwoStateExamples.lean` covers tables and joins. -/

namespace Belay.Sqlite.Model.TwoStateFixtures

open Syntax Resolution.CollationExamples Resolution.CompoundResolutionExamples Resolution.CommonTableResolutionExamples

-- A correlated subquery over the initial table reads the current outer row.
example : rows? (observe initialT joinCurrent
    (select [cellOf "x" "a", shown (.subquery 0)] (some (now "t" "x")) [] none [ascending (dotted "x" "a")]
      [countMatches])) = some (ints [[2, 1], [3, 0]]) := by decide +kernel

-- An EXCEPT between an initial term and a current term.
example : rows? (observe initialT joinCurrent
    (.select [] none [] none [] [] none none [termA (before "t"), termA (now "t")]
      none false (some (chain 0 [.except])))) = some (ints [[1]]) := by decide +kernel

-- A CTE named {lit}`t` does not shadow {lit}`before.t`, and shadows the current table.
example : rows? (observe initialT currentT
    (select [cell "a"] (some (before "t")) [] none [] [definition "t" (term [named (num "9") "a"])])) =
      some (ints [[1], [2]]) := by decide +kernel
example : rows? (observe initialT currentT
    (select [cell "a"] (some (now "t")) [] none [] [definition "t" (term [named (num "9") "a"])])) =
      some (ints [[9]]) := by decide +kernel

-- A view of the initial database expands in the initial context, also when the current table has the same name.
example : rows? (observe viewInitial currentT (selectA (before "v"))) = some (ints [[1], [2]]) := by decide +kernel
-- The current database has no view {lit}`v`.
example : code? (observe viewInitial currentT (selectA (now "v"))) = some 1 := by decide +kernel

example : code? (observe brokenViewInitial currentT (selectA (before "v"))) = some 1 := by decide +kernel

-- Parameters come from the ordinary evaluator context.
example : rows? (observe initialT currentT
    (selectA (before "t") (some (.compare .eq (named' "a") (.parameter 1)))) [.integer 2]) = some (ints [[2]]) := by
  decide +kernel

-- A clock reader needs a clock, as in the ordinary run.
example : refused (observe initialT currentT
    (select [shown (.currentTime "CURRENT_DATE")] (some (before "t")))) = true := by decide +kernel
example : rows? (observe initialT currentT
    (select [shown (.currentTime "CURRENT_DATE")] (some (before "t"))) [] (some fun _ => 212640249600000)) =
      some [[TimeKeyword.date.value 212640249600000], [TimeKeyword.date.value 212640249600000]] := by decide +kernel

-- A counter comes from the connection of the current database.
example : rows? (observe initialT currentT
    (select [shown (.call "changes" [])] (some (before "t"))) [] none { changes := some 8 }) =
      some (ints [[8], [8]]) := by decide +kernel
example : refused (observe initialT currentT (select [shown (.call "changes" [])] (some (before "t")))) = true := by
  decide +kernel

-- Name errors keep their classification.
example : code? (observe initialT currentT (select [cell "zz"] (some (before "t")))) = some 1 := by decide +kernel
example : code? (observe initialT currentT
    (select [shown (.qualified (name! "t") (name! "a"))] (some (before "t" "x")))) = some 1 := by decide +kernel

-- A query with no schema name gives the same output for several unrelated initial databases.
example : [initialT, currentT, databaseOf [], viewInitial].map (fun initial =>
    observe initial initialT (selectA (now "t"))) = List.replicate 4 (observe initialT initialT (selectA (now "t"))) := by
  decide +kernel

-- Without the two-state context, the ordinary run refuses {lit}`before.t`; it never reads the current {lit}`t`.
example : refused (runScriptStep context none 0 (connectionOf initialT)
    (selectA (before "t")) []).output = true := by decide +kernel
-- Another schema name is refused in the two-state context.
example : refused (observe initialT currentT
    (selectA { table := name! "t", alias := none, schema := some (name! "main") })) = true := by decide +kernel
-- A function call on {lit}`before` is refused.
example : refused (observe initialT currentT
    (select [cell "key"] (some { before "json_each" with arguments := some [.string [91, 93]] }))) = true := by
  decide +kernel

end Belay.Sqlite.Model.TwoStateFixtures
