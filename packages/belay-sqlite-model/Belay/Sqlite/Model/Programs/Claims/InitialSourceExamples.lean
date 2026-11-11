import Belay.Sqlite.Model.Programs.Scripts.QueryStepOutput
import Belay.Sqlite.Model.Schema.Dispatch.InitialSourceExamples

set_option doc.verso true

/-! Kernel examples for a source of the initial database (ADR 0017, S6): resolution gives
{lit}`before.t` the table position of the initial catalog, and the evaluator reads the rows of the initial
database for it and the rows of the current database for an ordinary source, also when both databases
have the same table name, different catalog positions or no table at all. -/

namespace Belay.Sqlite.Model.TwoStateFixtures

open Resolved Syntax Resolution.CollationExamples

/-- An initial database whose table {lit}`t` is at position 1, after a table {lit}`u`. -/
def twoTables : Database := databaseOf [tableOf "u" [col "b"] (ints [[9]]), tableOf "t" [col "a"] (ints [[5], [6]])]

/-- The connection to a database, with the given counters. -/
def connectionOf (database : Database) (counters : Counters := {}) : Connection := { state := { database, counters } }

/-- The rows of an output, or none for every other output. -/
def rows? : Output → Option (List (List Value))
  | .rows result => some result
  | .done _ | .error _ | .oneOf _ | .unmodeled _ => none

/-- The source {lit}`before.t` is at position 1 of the initial catalog, and {lit}`t` at position 0 of the
current one. A table that the initial database lacks is no source. -/
example : resolvedSources (before "t") twoTables = some [Source.initialTable 1] := by decide +kernel
example : resolvedSources (now "t") twoTables = some [Source.table 0] := by decide +kernel
example : resolvedSources (before "gone") twoTables = none := by decide +kernel

/-- The output of a query over the current database the current database (by default {lit}`currentT`) and the initial database {lit}`initial`, as
{name}`resolvedStepOutput` gives it for the resolved query, or none when resolution fails. -/
def stepOutputOf (query : Syntax.Subquery) (subqueries : List Syntax.Subquery) (initial : Database)
    (current : Database := currentT) : Option Output :=
  match resolveSelect context current.catalog query subqueries (some initial.catalog) with
  | .ok (resolved, _) => some (resolvedStepOutput none 0 (connectionOf current) [] resolved (some initial))
  | .error _ => none

/-- A scalar subquery reads the initial database too: {lit}`SELECT (SELECT count(*) FROM before.t) FROM t`
counts the rows of the initial {lit}`t` (two), and not the rows of the current {lit}`t` (one); the same
subquery over {lit}`t` counts the current rows. -/
example : (stepOutputOf (subqueryOf [shown (.subquery 0)] (now "t"))
    [subqueryOf [shown (.callStar "count")] (before "t")] initialT).bind rows? = some (ints [[2]]) := by
  decide +kernel
example : (stepOutputOf (subqueryOf [shown (.subquery 0)] (now "t"))
    [subqueryOf [shown (.callStar "count")] (now "t")] initialT).bind rows? = some (ints [[1]]) := by
  decide +kernel

/-- An initial source reads the initial rows, and an ordinary source the current rows. -/
example : rowsOf (.initialTable 1) (some twoTables) = some (ints [[5], [6]]) := by decide +kernel
example : rowsOf (.table 0) (some twoTables) = some (ints [[3]]) := by decide +kernel

/-- The same position in the two databases is two tables: position 0 is {lit}`u` of the initial database. -/
example : rowsOf (.initialTable 0) (some twoTables) = some (ints [[9]]) := by decide +kernel

example : rowsOf (.initialTable 7) (some twoTables) = none := by decide +kernel

end Belay.Sqlite.Model.TwoStateFixtures
