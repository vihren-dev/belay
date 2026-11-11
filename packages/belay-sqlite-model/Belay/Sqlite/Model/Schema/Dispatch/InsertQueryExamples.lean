import Belay.Sqlite.Model.Schema.Dispatch.NameTraceStatementExamples
import Belay.Sqlite.Model.Queries.Preparation.InsertQueryExamples

set_option doc.verso true

/-! Examples of the preparation of INSERT from a query ({lit}`resolveInsertQueryTraced`), checked by
{lit}`#guard`. The order of the checks is the order that the pinned SQLite 3.51.0 shows in native probes:
the table, the column list, the query, the numbers of columns, then the conflict clauses and RETURNING.
The catalog has the table {lit}`t(a, b, g)` with the generated column {lit}`g`, the view {lit}`v` and the
table {lit}`s(x, y, z)`. -/

namespace Belay.Sqlite.Model.InsertQueryExamples

open NameTraceStatementExamples (name column from_)

/-- The resolution of an INSERT from a query into the table, with the optional column list, over
{lean}`catalog`. -/
def run (table : String) (columns : Option (List String)) (source : Syntax.SelectBody)
    (conflicts : List Syntax.ConflictClause := []) (returning : List Syntax.ResultColumn := []) :=
  resolveStatement { profile := Profile.pinned, mode := .execution } { catalog }
    (.insertSelect (name table) (columns.map (·.map name)) source conflicts none returning)

-- A rowid name in the column list is a restriction, not the error that the table has no such column.
#guard refused (run "t" (some ["rowid"]) (body ["x"])) == some ([1], .rowidName)
#guard refused (run "t" (some ["b", "OID"]) (body ["x", "y"])) == some ([1], .rowidName)

-- The same holds for an INSERT of VALUES rows, which shares the check.
#guard refused (resolveStatement { profile := Profile.pinned, mode := .execution } { catalog }
    (.insert (name "t") (some [name "rowid"]) [[.null]] [] none [] [])) == some ([1], .rowidName)

-- An earlier unknown name stays the error of the table.
#guard prepared (run "t" (some ["nosuch", "rowid"]) (body ["x", "y"])) ==
  some (.expression (.tableHasNoColumn (name "t") (name "nosuch")))

-- A table that the catalog lacks is the error of the table before any error of the query.
#guard prepared (run "nosuch" none (body ["nosuch"])) == some (.noSuchTable (name "nosuch"))

-- A view is not writable, also with a query that has an error.
#guard prepared (run "v" none (body ["nosuch"])) == some (.viewModify (name "v"))

-- The column list is checked before the query: an unknown name is the error of the table.
#guard prepared (run "t" (some ["nosuch"]) (body ["nosuchcolumn"])) ==
  some (.expression (.tableHasNoColumn (name "t") (name "nosuch")))

-- A generated column in the list is refused before the query is resolved.
#guard prepared (run "t" (some ["g"]) (body ["nosuchcolumn"])) ==
  some (.expression (.insertGenerated (name "g")))

-- The query is resolved before the numbers of columns are compared.
#guard prepared (run "t" (some ["b"]) (body ["x", "y", "nosuch"])) ==
  some (.expression (.noSuchColumn (name "nosuch")))

-- A query column cannot name a column of the written table: {lit}`b` is no column of {lit}`s`.
#guard prepared (run "t" (some ["b"]) (body ["b"])) == some (.expression (.noSuchColumn (name "b")))

-- With a column list, the numbers of columns differ as {lit}`2 values for 1 columns`.
#guard prepared (run "t" (some ["b"]) (body ["x", "y"])) == some (.expression (.valuesForColumns 2 1))

-- Without a column list, the columns to fill are those that are not generated: two here.
#guard prepared (run "t" none (body ["x", "y", "z"])) == some (.expression (.valueCount (name "t") 2 3))

-- The numbers of columns are compared before the clauses and RETURNING are resolved.
#guard prepared (run "t" (some ["b"]) (body ["x", "y"]) []
    [.expression (column "nosuch") none "nosuch"]) == some (.expression (.valuesForColumns 2 1))

-- A RETURNING column that names no column of the written table is an error after the counts agree.
#guard prepared (run "t" (some ["b"]) (body ["x"]) []
    [.expression (column "nosuch") none "nosuch"]) == some (.expression (.noSuchColumn (name "nosuch")))

-- A column named twice in the list, with agreeing counts, is the restriction of INSERT: SQLite accepts it
-- and the model does not describe which value it stores.
#guard refused (run "t" (some ["b", "b"]) (body ["x", "y"])) == some ([1], .insertColumnTwice)

-- A statement that SQLite prepares is an INSERT from a query: the named column reads the first result
-- column, and the omitted columns have the cells of their defaults.
#guard cellsOf (run "t" (some ["b"]) (body ["x"])) ==
  some [.cell (.value .null), .source 0, .cell (.value .null)]

-- An INSERT without a column list fills the columns that are not generated, in table order.
#guard cellsOf (run "t" none (body ["x", "y"])) == some [.source 0, .source 1, .cell (.value .null)]

-- The names of the column list give the order of the result columns.
#guard cellsOf (run "t" (some ["b", "a"]) (body ["x", "y"])) == some [.source 1, .source 0, .cell (.value .null)]

-- A query of a table that the catalog lacks is a prepare error of the table.
#guard prepared (run "t" none (body ["x", "y"] "nosuch")) == some (.noSuchTable (name "nosuch"))

-- last_insert_rowid() in an INSERT from a query is a restriction, as in INSERT: the counter changes
-- with each row that the query streams. changes() is described.
#guard (refused (run "t" (some ["b"]) { body ["x"] with columns :=
    [.expression (.call "last_insert_rowid" []) none "last_insert_rowid()"] })).map (·.2) ==
  some .connectionCounterRead
#guard (refused (run "t" (some ["b"]) { body ["x"] with columns :=
    [.expression (.call "changes" []) none "changes()"] })).isNone

end Belay.Sqlite.Model.InsertQueryExamples
