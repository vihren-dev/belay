import Belay.Sqlite.Resolution.QueryResolutionExamples
import Belay.Sqlite.RowDelete

set_option doc.verso true

/-! Examples of DELETE (ADR 0012, amendment 1, slice 3c), checked by {lit}`#guard`: its
resolution, its prepare errors and restrictions, and the rows that it removes. -/

namespace Belay.Sqlite.Resolution.DeleteExamples
open Belay.Sqlite Syntax Resolution.Examples Resolution.QueryResolutionExamples

/-- The filter {lit}`Abc = 1` as written. -/
def abcIsOne : Syntax.Expr := .compare .eq (.identifier "Abc" .none) (.numeric "1")

-- The filter resolves as a SELECT condition; RETURNING `*` names the table's columns.
#guard resolvedOne (.delete "t" (some abcIsOne)) ==
  some (.delete 0 (some (.compare .eq (some .integer) (.column 0) (.literal (.integer 1)))) [])
#guard resolvedOne ((.delete "t" none [.star])) ==
  some (.delete 0 none [(.column 0, "Abc"), (.column 1, "b")])
-- SQLite's prepare errors, and SQLite's own tables as a restriction.
#guard errorOf (.delete "missing" none) == some (.noSuchTable "missing")
#guard errorOf (.delete "t" (some (.compare .eq (.identifier "zz" .none) (.numeric "1")))) == some (.noSuchColumn "zz")
#guard restrictedOne (.delete "sqlite_schema" none)

/-- A table with a row where {lit}`Abc` is 1 and a row where it is NULL. -/
def table : Table :=
  { shape := { columns := [{ name := "Abc", declaredType := some "INTEGER" },
      { name := "b", declaredType := some "TEXT" }] },
    rows := [{ rowid := 1, values := [.integer 1, .text [97]] }, { rowid := 2, values := [.null, .text [98]] }] }

-- The row where the filter is true is removed; the row where it is NULL is kept.
#guard (LiteralData.deleted table (some (.compare .eq none (.column 0) (.literal (.integer 1))))).rows ==
  [{ rowid := 2, values := [.null, .text [98]] }]
-- Without a filter every row is removed.
#guard (LiteralData.deleted table none).rows == []

end Belay.Sqlite.Resolution.DeleteExamples
