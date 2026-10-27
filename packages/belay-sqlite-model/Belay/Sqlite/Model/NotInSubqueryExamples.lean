import Belay.Sqlite.Model.Execution
import Belay.Sqlite.Model.QueryExamples
import Belay.Sqlite.Model.NotInRowidAlias

set_option doc.verso true

/-! Checked examples of {lit}`x NOT IN (SELECT c FROM u)` against the correlated
{lit}`NOT EXISTS (SELECT 1 FROM u WHERE u.c = x)` (task 20261027), as queries over a concrete database. The
outer table is {lit}`t(k)` at position 0 and the table of the subquery is {lit}`u(c)` at position 1. Native SQLite is the
authority for these values: its results for the same statements are in the surface tests of the NOT IN task. When
no value is NULL, the two queries keep the same rows. A NULL probe, a NULL candidate and a collation of the
comparison that differs from the collation of the {lit}`IN` test each give a case where they keep different rows. -/

namespace Belay.Sqlite.Model.Resolved.NotInSubqueryExamples

/-- The table with one column {lit}`name` and the given cells as rows, with rowids 1, 2, and so on. -/
def oneColumn (cells : List Value) : Table where
  shape := { columns := [{ name := (name! "x"), declaredType := none }] }
  rows := (cells.zipIdx 1).map fun (cell, rowid) => ⟨rowid, [cell]⟩

/-- The database with the outer table {lit}`t` at position 0 and the table {lit}`u` of the subquery at position 1. -/
def database (outerCells subqueryCells : List Value) : Database :=
  .ofTables [((name! "t"), oneColumn outerCells), ((name! "u"), oneColumn subqueryCells)]

/-- {lit}`SELECT k FROM t WHERE x NOT IN (SELECT c FROM u)`, with the collation of the {lit}`IN` test. The outer
query has one column, so the subquery sees one outer cell. -/
def keysNotIn (collation : Collation) : Query × List Query :=
  ({ sources := [.first 0], filter := some (.inQuery (.column 0) 0 (some .numeric) collation true),
     aggregate := false, groupBy := [], columns := [.scalar (.column 0)], names := ["k"], orderBy := [], offset := 0,
     limit := none }, [Query.columnOf 1 1 0 ["c"]])

/-- {lit}`SELECT k FROM t WHERE NOT EXISTS (SELECT 1 FROM u WHERE u.c = k)`, with the collation of the comparison. -/
def keysNotExists (collation : Collation) : Query × List Query :=
  ({ (keysNotIn .binary).1 with filter := some (.not (.exists 0)) },
   [Query.matchingKey 1 1 0 0 (some .numeric) collation ["1"]])

/-- The rows of a query with its subqueries over a database, at clock 0. -/
def rowsOn (database : Database) (statement : Query × List Query) : Option (List (List Value)) :=
  (statement.1.runOn 0 {} [] database statement.2).map (·.2.rows)

-- No NULL: 1 and 4 are in no row of u and are kept by both queries; 2 and 3 match and are dropped by both.
example : rowsOn (database [.integer 1, .integer 2, .integer 3, .integer 4] [.integer 2, .integer 3])
    (keysNotIn .binary) = some [[.integer 1], [.integer 4]] := by decide +kernel
example : rowsOn (database [.integer 1, .integer 2, .integer 3, .integer 4] [.integer 2, .integer 3])
    (keysNotExists .binary) = some [[.integer 1], [.integer 4]] := by decide +kernel

-- An empty subquery keeps every row in both queries, also the row with the NULL key.
example : rowsOn (database [.integer 1, .null] []) (keysNotIn .binary) = some [[.integer 1], [.null]] := by
  decide +kernel
example : rowsOn (database [.integer 1, .null] []) (keysNotExists .binary) = some [[.integer 1], [.null]] := by
  decide +kernel

-- A NULL probe breaks the premise: NOT IN is NULL for the row with the NULL key, NOT EXISTS is 1.
example : rowsOn (database [.integer 1, .null] [.integer 2]) (keysNotIn .binary) = some [[.integer 1]] := by
  decide +kernel
example : rowsOn (database [.integer 1, .null] [.integer 2]) (keysNotExists .binary) =
    some [[.integer 1], [.null]] := by decide +kernel

-- A NULL candidate breaks the premise: NOT IN is NULL for the key 1, which no candidate matches; NOT EXISTS keeps it.
example : rowsOn (database [.integer 1, .integer 2] [.integer 2, .null]) (keysNotIn .binary) = some [] := by
  decide +kernel
example : rowsOn (database [.integer 1, .integer 2] [.integer 2, .null]) (keysNotExists .binary) =
    some [[.integer 1]] := by decide +kernel

-- Text keys: the key A equals the candidate a under NOCASE and differs from it under BINARY, so the two queries
-- agree when both use the same collation and differ when the collations differ.
example : rowsOn (database [.text [65]] [.text [97]]) (keysNotIn .nocase) = some [] := by decide +kernel
example : rowsOn (database [.text [65]] [.text [97]]) (keysNotExists .nocase) = some [] := by decide +kernel
example : rowsOn (database [.text [65]] [.text [97]]) (keysNotIn .binary) = some [[.text [65]]] := by
  decide +kernel
example : rowsOn (database [.text [65]] [.text [97]]) (keysNotExists .binary) = some [[.text [65]]] := by
  decide +kernel
example : rowsOn (database [.text [65]] [.text [97]]) (keysNotExists .nocase) ≠
    rowsOn (database [.text [65]] [.text [97]]) (keysNotIn .binary) := by decide +kernel

end Belay.Sqlite.Model.Resolved.NotInSubqueryExamples
