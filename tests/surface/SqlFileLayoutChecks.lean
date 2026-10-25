import Belay
import Belay.Sqlite.SqlFileLayout
import Belay.Sqlite.SqlFileDiagnostics

open Belay.Sqlite

/-! A fixture of `tests/surface_sql_file_forms_test.py`: the pure parts of the SQL-file forms
(`Belay/Sqlite/SqlFileLexer.lean`, `SqlFileMarkers.lean`, `SqlFileLayout.lean` and
`SqlFileDiagnostics.lean`), over small texts. A failing `#guard` fails the file. -/

/-- The comments of a text as `(start, stop, isLine)`. -/
def commentRanges (text : String) : List (Nat × Nat × Bool) :=
  (sqlComments text.toUTF8).toList.map fun comment => (comment.start, comment.stop, comment.isLine)

-- Quotes hide comment starts, a doubled quote stays inside, and a block comment ends at its closer.
#guard commentRanges "SELECT '--a', \"--b\", `--c`, [--d] -- e" == [(34, 38, true)]
#guard commentRanges "SELECT 'it''s -- not', 1 /* a -- b */ -- c\n" == [(25, 37, false), (38, 42, true)]
#guard commentRanges "-- unterminated block /* x" == [(0, 26, true)]
#guard commentRanges "/* never closed" == [(0, 15, false)]

/-- The structure of a text whose statements are given by their byte ranges. -/
def structureOf (text : String) (ranges : List (Nat × Nat)) : FileStructure :=
  FileStructure.ofRanges text.toUTF8 ranges.toArray

/-- The names that `selectNamed` finds, or its message. -/
def namesOf (text : String) (ranges : List (Nat × Nat)) : Except String (List String) :=
  match selectNamed (structureOf text ranges) with
  | .ok entries => .ok (entries.toList.map (·.name))
  | .error problem => .error problem.message

#guard namesOf "-- name: a\nSELECT 1;\n-- name: b\nSELECT 2;\n" [(11, 19), (32, 40)] == .ok ["a", "b"]
#guard namesOf "-- just comments\n" [] == .ok []
#guard namesOf "SELECT 1;\n-- name: a\nSELECT 2;\n" [(0, 8), (22, 30)] ==
  .error "SQL without a name; put a -- name: marker before it"
-- A marker inside the statement is part of the statement, not a name.
#guard namesOf "-- name: a\nSELECT 'x' -- name: b\n;\n" [(11, 21)] == .ok ["a"]

-- A tool's text is explained only where the parser refused it.
#guard (toolSyntaxHint "SELECT 1;\n  .mode csv\n".toUTF8 12).isSome
#guard (toolSyntaxHint "SELECT 1;\n.5\n".toUTF8 10).isNone
#guard (toolSyntaxHint "SELECT sqlc.arg(id)".toUTF8 15).isSome
#guard (toolSyntaxHint "SELECT arg(id)".toUTF8 10).isNone
#guard (toolSyntaxHint "".toUTF8 0).isNone
