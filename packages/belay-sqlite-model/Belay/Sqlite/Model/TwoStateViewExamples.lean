import Belay.Sqlite.Model.TwoStateExamples

set_option doc.verso true

/-! Kernel checks of the observation of a query over two databases (ADR 0017, S6) for views, common
tables, subqueries, compounds, parameters, clocks, counters, errors and refusals.
{lit}`TwoStateExamples.lean` covers tables and joins. -/

namespace Belay.Sqlite.Model.TwoStateFixtures

open Syntax Resolution.Examples Resolution.CollationExamples Resolution.CompoundResolutionExamples
  Resolution.CommonTableResolutionExamples

/-- A term {lit}`SELECT a FROM source`, in the query {lit}`parent`. -/
def termA (source : TableReference) (parent : Option Nat := none) : Subquery :=
  { columns := [cell "a"], source := some source, joins := [], filter := none, groupBy := [], orderBy := [],
    limit := none, offset := none, parent }

/-- A scalar subquery {lit}`(SELECT count(*) FROM before.t AS i WHERE i.a = x.a)`, inside the statement's query. -/
def countMatches : Subquery :=
  { columns := [shown (.callStar "count")], source := some (before "t" "i"), joins := [],
    filter := some (.compare .eq (dotted "i" "a") (dotted "x" "a")), groupBy := [], orderBy := [],
    limit := none, offset := none, parent := none }

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

/-- The initial database has {lit}`t(a)` and the view {lit}`v` as {lit}`SELECT a FROM t`. -/
def viewInitial : Database :=
  { catalog := [{ name := name! "t", entry := .table { columns := [col "a"] } },
                { name := name! "v", entry := .view { query := termA (now "t") } }],
    rows := [(ints [[1], [2]]).zipIdx.map fun (values, index) => { rowid := ((index + 1 : Nat) : Int), values }, []] }

-- A view of the initial database expands in the initial context, also when the current table has the same name.
example : rows? (observe viewInitial currentT (selectA (before "v"))) = some (ints [[1], [2]]) := by decide +kernel
-- The current database has no view {lit}`v`.
example : code? (observe viewInitial currentT (selectA (now "v"))) = some 1 := by decide +kernel

/-- The initial database has a view {lit}`v` of a table that it lacks. -/
def brokenViewInitial : Database :=
  { catalog := [{ name := name! "v", entry := .view { query := termA (now "gone") } }], rows := [[]] }
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
