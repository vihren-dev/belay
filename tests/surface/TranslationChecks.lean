import Belay

/-! A fixture of `tests/surface_translation_checks_test.py`: checks of the translation of the text
package (`Belay.Sqlite.Translation`) that need its Lean values, not the program's JSON. A model
restriction names a statement and a node path, so each statement's ranges must have the shape of
the path steps: a path selects the range of the node that it names, or of its deepest known part.
`dequote` follows SQLite, `valueRows` refuses a VALUES node of a shape that the grammar does not
make, and the binding refuses a parse document for another grammar than the one it asked for
(`decodeParse`). The file fails to elaborate when a check fails. -/

open Belay.Sqlite Belay.Sqlite.Model Belay.Sqlite.Translation

/-- The range that a model path selects: each step is a part's position; a step past the known
parts stops at the node before it. -/
def Belay.Sqlite.Translation.Span.select (span : Span) : List Nat → Nat × Nat
  | [] => (span.start, span.stop)
  | step :: rest => match span.parts[step]? with
    | some part => part.select rest
    | none => (span.start, span.stop)

/-- The text of the range that the path selects in the statement. -/
def textAt (sql : String) (item : Located Syntax.Statement) (path : List Nat) : String :=
  let (start, stop) := item.span.select path
  (String.fromUTF8? (sql.toUTF8.extract start stop)).getD ""

/-- The statements of the SQL with the default release's grammar; a refusal fails the check. -/
def translated (sql : String) : IO (Array (Located Syntax.Statement)) := do
  let grammar ← IO.ofExcept ((selectGrammar (← loadedMetadata) Release.default).mapError IO.userError)
  match ← translate grammar sql.toUTF8 with
  | .ok items => return items
  | .error refusal => throw <| IO.userError s!"the translation refuses {sql}: {refusal.message}"

/-- Fail with the check's name when the text at the path is not the expected text. -/
def expectText (sql : String) (item : Located Syntax.Statement) (path : List Nat) (expected : String) : IO Unit := do
  let found := textAt sql item path
  unless found == expected do throw <| IO.userError s!"path {path} selects {repr found}, not {repr expected}"

#eval show IO Unit from do
  let sql := "CREATE TABLE t(a, rowid TEXT); INSERT INTO t(a) VALUES (1), (2.5); UPDATE t SET a = 1, b = -x;"
  let #[created, inserted, updated] ← translated sql | throw <| IO.userError "expected three statements"
  expectText sql created [1, 1] "rowid TEXT"
  expectText sql inserted [2, 1, 0] "2.5"
  expectText sql updated [1, 1, 1, 0] "x"
  expectText sql updated [1, 1, 1, 0, 9] "x"
  let query := "SELECT a FROM t WHERE EXISTS (SELECT 1 FROM u WHERE b = a);"
  let #[selected] ← translated query | throw <| IO.userError "expected one statement"
  expectText query selected [8, 0, 3] "b = a"

#guard ["\"a\"\"b\"", "[a]]", "`x`", "'it''s'", "\"Some\" Type", "plain"].map dequote ==
  ["a\"b", "a]", "x", "it's", "Some", "plain"]

/-- A VALUES list node whose last part is a comma, which the grammar never makes. -/
def malformedValues : SqlTree :=
  { sql := ",".toUTF8, nodes := #[⟨"COMMA", 0, 1, #[]⟩, ⟨"mvalues", 0, 1, #[0]⟩, ⟨"oneselect", 0, 1, #[1]⟩,
      ⟨"selectnowith", 0, 1, #[2]⟩, ⟨"select", 0, 1, #[3]⟩] }

#guard match (valueRows malformedValues malformedValues.nodes[4]!).run' {} with
  | .error refusal => refusal.status == "UNSUPPORTED" &&
      (refusal.message.splitOn "rewrite it with the modeled forms").length > 1
  | .ok _ => false

/-- A parse document of the library for the grammar {lit}`b`. -/
def otherGrammarDocument : String := "{\"status\":\"PARSED\",\"grammar\":\"b\",\"nodes\":[],\"root\":0}"

#guard match decodeParse "a" 0 otherGrammarDocument with
  | .error message => message == "the result is for another grammar"
  | .ok _ => false
