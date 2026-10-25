import Belay.Sqlite.SqlSourceRecord
import Belay.Sqlite.SqlCheckReport

open Belay.Sqlite Lean

/-! A fixture of `tests/surface_sql_records_test.py`: the pure parts of the compiled SQL-source
record (`Belay/Sqlite/SqlSourceRecord.lean`) and of the checker's report (`Belay/Sqlite/SqlCheckReport.lean`). A failing `#guard` fails the file. -/

-- Line endings do not change the hash, as in Lake's text inputs; other edits do.
#guard sqlTextHash "SELECT 1;\r\nSELECT 2;\r\n" == sqlTextHash "SELECT 1;\nSELECT 2;\n"
#guard sqlTextHash "SELECT 1;\n" != sqlTextHash "SELECT 2;\n"
#guard sqlTextHash "SELECT 1;\n" != sqlTextHash "SELECT 1;"

/-- A record of a file used by a declaration. -/
def used (declaration : Option Name) : SqlSourceUse :=
  { package := "pkg", path := "sql/a.sql", hash := sqlTextHash "SELECT 1;", declaration }

-- Several declarations that use one file are several records of one source.
#guard (used (some `a)).sameSource (used (some `b))
#guard !(used none).sameSource { used none with path := "sql/b.sql" }
#guard !(used none).sameSource { used none with hash := 0 }
#guard !(used none).sameSource { used none with package := "other" }
#guard (dedupeSqlSourceUses [used none, used (some `a), used none, used (some `a)]).size == 2

-- A file is fresh only with the recorded hash; a file that is gone is missing.
#guard sourceState 5 (some 5) == .fresh
#guard sourceState 5 (some 6) == .changed
#guard sourceState 5 none == .missing

/-- A checked library with one fresh and one stale source. -/
def mixed : LibraryCheck :=
  { library := "Lib", modules := 2, sources := #[
      { package := "pkg", path := "sql/a.sql", state := .fresh, declarations := #[`a] },
      { package := "pkg", path := "sql/b.sql", state := .changed, declarations := #[`b, `c] }] }

-- A library with no SQL sources reports zero and has nothing stale.
#guard ({ library := "Empty", modules := 3, sources := #[] } : LibraryCheck).render ==
  "library Empty: 3 modules, 0 SQL sources, 0 stale"
#guard mixed.stale.size == 1
#guard (mixed.render.splitOn "\n").length == 3
#guard (mixed.render.splitOn "\n")[1]! ==
  "  pkg: sql/b.sql changed since the library was built (used by b, c); rebuild with: lake build Lib"

-- Zero only when every source is fresh; a stale source is 1; a library that could not be read is 2.
#guard exitCodeOf #[] #[] == 0
#guard exitCodeOf #[mixed] #[] == 1
#guard exitCodeOf #[mixed] #["cannot read"] == 2
