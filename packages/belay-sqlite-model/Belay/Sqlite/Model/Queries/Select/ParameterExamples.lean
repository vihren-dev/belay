import Belay.Sqlite.Model.Queries.Fixtures.Examples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.ParameterExamples

open Belay.Sqlite.Model Syntax

/-- The row of the examples. -/
def row : List Value := [.integer 1, .text [49]]

/-- A name as written, without quotes. -/
def col (text : String) : Expr := .identifier (Identifier.ofString text) .none

/-- The table {lit}`t` in {lit}`FROM`. -/
def fromT : Option TableReference := some { table := name! "t", alias := none }

/-- {lit}`SELECT i FROM t LIMIT limit OFFSET offset`. -/
def windowed (limit offset : Option Expr) : Syntax.Statement :=
  .select [.expression (col "i") none "i"] fromT [] none [] [] limit offset

end Belay.Sqlite.Model.Resolution.ParameterExamples
