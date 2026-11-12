import Belay.Sqlite.Model.Queries.Evaluation.TwoStateExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.TwoStateFixtures

open Syntax Resolution.CollationExamples

/-- A term {lit}`SELECT a FROM source`, in the query {lit}`parent`. -/
def termA (source : TableReference) (parent : Option Nat := none) : Subquery :=
  { columns := [cell "a"], source := some source, joins := [], filter := none, groupBy := [], orderBy := [],
    limit := none, offset := none, parent }

/-- A scalar subquery {lit}`(SELECT count(*) FROM before.t AS i WHERE i.a = x.a)`, inside the statement's query. -/
def countMatches : Subquery :=
  { columns := [shown (.callStar "count")], source := some (before "t" "i"), joins := [],
    filter := some (.compare .eq (dotted "i" "a") (dotted "x" "a")), groupBy := [], orderBy := [],
    limit := none, offset := none, parent := none }

/-- The initial database has {lit}`t(a)` and the view {lit}`v` as {lit}`SELECT a FROM t`. -/
def viewInitial : Database :=
  { catalog := [{ name := name! "t", entry := .table { columns := [col "a"] } },
                { name := name! "v", entry := .view { query := termA (now "t") } }],
    rows := [(ints [[1], [2]]).zipIdx.map fun (values, index) => { rowid := ((index + 1 : Nat) : Int), values }, []] }

/-- The initial database has a view {lit}`v` of a table that it lacks. -/
def brokenViewInitial : Database :=
  { catalog := [{ name := name! "v", entry := .view { query := termA (now "gone") } }], rows := [[]] }

end Belay.Sqlite.Model.TwoStateFixtures
