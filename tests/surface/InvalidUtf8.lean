import Belay

/-! A fixture of `tests/surface_parser_test.py`: the binding passes the SQL as bytes
(`Belay.Sqlite.ParserLibrary.parse`), so bytes that are not UTF-8 reach the parser library, which
refuses the text as a grammar error at offset 0. The text is `SELECT 'a` and the byte 0xFF, then
`';`. -/

open Belay.Sqlite

#eval show IO Unit from do
  let sql := "SELECT 'a".toUTF8.push 0xFF ++ "';".toUTF8
  IO.println s!"invalid UTF-8: {repr (← parseSql Release.default sql)}"
