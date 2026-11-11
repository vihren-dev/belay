import Belay.Sqlite.Model.Queries.Preparation.RenameCatalogExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.DropColumnExamples

open Belay.Sqlite.Model Syntax

/-- The text {lit}`b > 0` with the token of the column {lit}`b`, the second column. -/
def positiveB : SourceText := { text := "b > 0", tokens := [{ paths := [[1]], start := 0, stop := 1, quote := .none }] }

/-- The text {lit}`A > 0` with the token of the column {lit}`a`, spelled with a capital. -/
def positiveUpperA : SourceText := { text := "A > 0", tokens := [{ paths := [[1]], start := 0, stop := 1, quote := .none }] }

end Belay.Sqlite.Model.Resolution.DropColumnExamples
