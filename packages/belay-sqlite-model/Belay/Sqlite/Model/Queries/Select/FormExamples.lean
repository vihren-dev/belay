import Belay.Sqlite.Model.Queries.Fixtures.Examples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.FormExamples

open Belay.Sqlite.Model Syntax

/-- A catalog with {lit}`t(i INTEGER, s TEXT, n TEXT COLLATE NOCASE)` at position 0. -/
def catalog : Catalog :=
  [{ name := (name! "t"), entry := .table { columns := [{ name := (name! "i"), declaredType := some "INTEGER" },
      { name := (name! "s"), declaredType := some "TEXT" },
      { name := (name! "n"), declaredType := some "TEXT", collation := .nocase }] } }]

/-- The row of the examples. -/
def row : List Value := [.integer 1, .text [49], .text [65]]

/-- A name as written, without quotes. -/
def col (text : String) : Expr := .identifier (Identifier.ofString text) .none

/-- A string literal of ASCII text. -/
def str (text : String) : Expr := .string text.toUTF8.toList

/-- {lit}`value COLLATE BINARY`. -/
def binary (value : Expr) : Expr := .collate value (Identifier.ofString "BINARY")

end Belay.Sqlite.Model.Resolution.FormExamples
