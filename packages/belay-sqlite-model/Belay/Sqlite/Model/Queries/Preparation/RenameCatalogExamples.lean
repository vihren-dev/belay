import Belay.Sqlite.Model.Queries.Preparation.RewriteExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.RenameCatalogExamples

open Belay.Sqlite.Model Syntax

/-- The text {lit}`a > 0` with the token of the column. -/
def positive : SourceText := { text := "a > 0", tokens := [{ paths := [[1]], start := 0, stop := 1, quote := .none }] }

/-- The text {lit}`"z"` of a result column, and the same text after the quote is fixed: a result column
without an alias has its text as its name. -/
def doubleQuotedText : SourceText :=
  { text := "\"z\"", tokens := [{ paths := [[]], start := 0, stop := 3, quote := .double }] }

/-- The text {lit}`'z'` that SQLite writes for {lit}`doubleQuotedText`. -/
def singleQuotedText : SourceText :=
  { text := "'z'", tokens := [{ paths := [[]], start := 0, stop := 3, quote := .single }] }

end Belay.Sqlite.Model.Resolution.RenameCatalogExamples
