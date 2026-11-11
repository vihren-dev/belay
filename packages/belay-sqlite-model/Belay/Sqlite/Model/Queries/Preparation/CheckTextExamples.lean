import Belay.Sqlite.Model.Queries.Fixtures.Examples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.CheckTextExamples

open Belay.Sqlite.Model Syntax

/-- The text {lit}`t.b > 0 and "a" < 5` with its three name tokens, as the translator writes them. -/
def source : SourceText :=
  { text := "t.b > 0 and \"a\" < 5", tokens := [
    { paths := [[0, 1, 0]], start := 0, stop := 1, quote := .none },
    { paths := [[0, 1, 1]], start := 2, stop := 3, quote := .none },
    { paths := [[1, 1], [1, 1, 0], [1, 1, 1]], start := 12, stop := 15, quote := .double }] }

/-- The condition of {name}`source`. -/
def condition : Expr :=
  .and (.compare .gt (.qualified (name! "t") (name! "b")) (.numeric "0"))
    (.compare .lt (.identifier (name! "a") .double) (.numeric "5"))

end Belay.Sqlite.Model.Resolution.CheckTextExamples
