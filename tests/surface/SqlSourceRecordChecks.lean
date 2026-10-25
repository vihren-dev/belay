import Belay.Sqlite.SqlSourceRecord

open Belay.Sqlite Lean

/-! A fixture of `tests/surface_sql_records_test.py`: the pure parts of the compiled SQL-source
record (`Belay/Sqlite/SqlSourceRecord.lean`). A failing `#guard` fails the file. -/

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
