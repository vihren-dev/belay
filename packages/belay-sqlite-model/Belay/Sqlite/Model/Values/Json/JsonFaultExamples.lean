import Belay.Sqlite.Model.Shared.Catalog.Database

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved.JsonFaultExamples

/-- The text of a string, as a literal. -/
def text (string : String) : Expr := .literal (.text string.toUTF8.toList)

/-- {lit}`json_extract('x', '$')`, which fails with {lit}`malformed JSON`. -/
def malformed : Expr := .json .extract (.cons (text "x") (.cons (text "$") .nil))

/-- {lit}`json_extract('{"a":1}', '$.a')`, which is 1. -/
def selected : Expr := .json .extract (.cons (text "{\"a\":1}") (.cons (text "$.a") .nil))

/-- {lit}`SELECT json_extract('x', '$')`: a query without {lit}`FROM`. -/
def fromless : Query where
  sources := []
  filter := none
  aggregate := false
  groupBy := []
  columns := [.scalar malformed]
  names := ["v"]
  orderBy := []
  offset := 0
  limit := none

/-- An empty table {lit}`t(a)` at catalog position 0. -/
def empty : Database :=
  .ofTables [((name! "t"), { shape := { columns := [{ name := (name! "a"), declaredType := none }] }, rows := [] })]

end Belay.Sqlite.Model.Resolved.JsonFaultExamples
