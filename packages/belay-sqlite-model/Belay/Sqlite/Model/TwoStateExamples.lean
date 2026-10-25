import Belay.Sqlite.Model.TwoStateFixtureExamples

set_option doc.verso true

/-! Kernel checks of the observation of a query over two databases (ADR 0017, S6), for tables and
joins. The same SQL runs against native SQLite 3.51.0 with an attached copy named {lit}`before` in
{lit}`tests/surface_two_state_test.py`. {lit}`TwoStateViewExamples.lean` covers views, common
tables, subqueries, parameters, clocks, counters and refusals. -/

namespace Belay.Sqlite.Model.TwoStateFixtures

open Syntax Resolution.Examples Resolution.CollationExamples Resolution.CompoundResolutionExamples

-- The source {lit}`before.t` reads the initial rows and {lit}`t` the current rows.
example : rows? (observe initialT currentT (selectA (before "t"))) = some (ints [[1], [2]]) := by decide +kernel
example : rows? (observe initialT currentT (selectA (now "t"))) = some (ints [[3]]) := by decide +kernel

-- Equal databases give the same rows for both origins.
example : rows? (observe initialT initialT (selectA (before "t"))) = some (ints [[1], [2]]) := by decide +kernel
example : rows? (observe initialT initialT (selectA (now "t"))) = some (ints [[1], [2]]) := by decide +kernel

-- The current database has no table: {lit}`before.t` still reads the initial one.
example : rows? (observe initialT (databaseOf []) (selectA (before "t"))) = some (ints [[1], [2]]) := by decide +kernel
example : code? (observe initialT (databaseOf []) (selectA (now "t"))) = some 1 := by decide +kernel

-- The initial database has no table: {lit}`no such table: before.t`, whatever the current database has.
example : code? (observe (databaseOf []) currentT (selectA (before "t"))) = some 1 := by decide +kernel
example : code? (observe (databaseOf [tableOf "u" [col "a"] []]) currentT (selectA (before "t"))) = some 1 := by
  decide +kernel

/-- The initial database has {lit}`u` and then {lit}`t(a)`; the current database has {lit}`t(x, y)`. -/
def movedInitial : Database :=
  databaseOf [tableOf "u" [col "b"] (ints [[7]]), tableOf "t" [col "a"] (ints [[5], [6]])]

/-- The current database has {lit}`t(x, y)` at position 0. -/
def movedCurrent : Database := databaseOf [tableOf "t" [col "x", col "y"] (ints [[1, 2]])]

-- Another position and another schema: the columns and rows of {lit}`before.t` come from the initial catalog.
example : rows? (observe movedInitial movedCurrent (selectA (before "t"))) = some (ints [[5], [6]]) := by decide +kernel
example : code? (observe movedInitial movedCurrent (selectA (now "t"))) = some 1 := by decide +kernel
example : rows? (observe movedInitial movedCurrent
    (select [cell "x"] (some (now "t")))) = some (ints [[1]]) := by decide +kernel

-- A rowid alias (INTEGER PRIMARY KEY) in both tables, with other rows in the current table. The model
-- refuses the names rowid, _rowid_ and oid, so only the alias name reads the rowid.
/-- The initial table {lit}`t(id, a)` whose column {lit}`id` is the rowid alias, with two rows. -/
def aliasInitial : Database :=
  databaseOf [tableOf "t" [col "id", col "a"] (ints [[1, 10], [2, 20]]) (alias := some 0)]
/-- The current table {lit}`t(id, a)` with the same alias and one other row. -/
def aliasCurrent : Database :=
  databaseOf [tableOf "t" [col "id", col "a"] (ints [[1, 99]]) (alias := some 0)]
example : rows? (observe aliasInitial aliasCurrent
    (select [cell "id", cell "a"] (some (before "t")) [] none [ascending (named' "id")])) =
      some (ints [[1, 10], [2, 20]]) := by decide +kernel

-- A NOCASE column of the initial table and a BINARY column of the current table.
/-- The initial table {lit}`t(a TEXT COLLATE NOCASE)` with the row {lit}`'x'`. -/
def nocaseInitial : Database := databaseOf [tableOf "t" [col "a" (some "TEXT") .nocase] [[text "x"]]]
/-- The current table {lit}`t(a TEXT)` with the row {lit}`'x'` and the default BINARY collation. -/
def binaryCurrent : Database := databaseOf [tableOf "t" [col "a" (some "TEXT")] [[text "x"]]]
example : rows? (observe nocaseInitial binaryCurrent
    (selectA (before "t") (some (.compare .eq (named' "a") (.string [88]))))) = some [[text "x"]] := by decide +kernel
example : rows? (observe nocaseInitial binaryCurrent
    (selectA (now "t") (some (.compare .eq (named' "a") (.string [88]))))) = some [] := by decide +kernel

-- INTEGER affinity in the initial table converts the text {lit}`'1'`; a column without a type does not.
/-- The initial table {lit}`t(a INTEGER)` with the row 1. -/
def integerInitial : Database := databaseOf [tableOf "t" [col "a"] (ints [[1]])]
/-- The current table {lit}`t(a)` with no declared type and the row 1. -/
def untypedCurrent : Database := databaseOf [tableOf "t" [col "a" none] (ints [[1]])]
example : rows? (observe integerInitial untypedCurrent
    (selectA (before "t") (some (.compare .eq (named' "a") (.string [49]))))) = some (ints [[1]]) := by decide +kernel
example : rows? (observe integerInitial untypedCurrent
    (selectA (now "t") (some (.compare .eq (named' "a") (.string [49]))))) = some [] := by decide +kernel

-- A left join of a current table to an initial table extends the unmatched row with NULL.
/-- The current table {lit}`t(a INTEGER)` with the rows 2 and 3, which a join with the initial rows 1 and 2 matches. -/
def joinCurrent : Database := databaseOf [tableOf "t" [col "a"] (ints [[2], [3]])]
example : rows? (observe initialT joinCurrent
    (select [cellOf "x" "a", cellOf "i" "a"] (some (now "t" "x"))
      [{ operator := ["LEFT"], source := before "t" "i",
         condition := some (.compare .eq (dotted "i" "a") (dotted "x" "a")), usingColumns := none }]
      none [ascending (dotted "x" "a")])) = some [[.integer 2, .integer 2], [.integer 3, .null]] := by decide +kernel

-- The same table name in both origins, joined: each name reads its own database.
example : rows? (observe initialT joinCurrent
    (select [cellOf "i" "a", cellOf "c" "a"] (some (before "t" "i"))
      [{ operator := [], source := now "t" "c", condition := none, usingColumns := none }]
      (some (.compare .eq (dotted "i" "a") (dotted "c" "a"))) [])) = some (ints [[2, 2]]) := by decide +kernel

-- An alias named {lit}`before` is a source name, not the schema.
example : rows? (observe initialT currentT
    (select [cellOf "before" "a"] (some (now "t" "before")))) = some (ints [[3]]) := by decide +kernel
example : rows? (observe initialT currentT
    (select [cellOf "before" "a"] (some (before "t" "before")) [] none [ascending (dotted "before" "a")])) =
      some (ints [[1], [2]]) := by decide +kernel

-- A quoted table name that contains a dot is one name.
/-- The initial table named {lit}`"a.b"`, whose name has a dot, with the row 4. -/
def dottedInitial : Database := databaseOf [tableOf "a.b" [col "a"] (ints [[4]])]
example : rows? (observe dottedInitial currentT (selectA (before "a.b"))) = some (ints [[4]]) := by decide +kernel
example : code? (observe dottedInitial currentT (selectA (before "a"))) = some 1 := by decide +kernel

end Belay.Sqlite.Model.TwoStateFixtures
