import Belay
import Belay.Sqlite.SqlFileTerm

open Belay.Sqlite Lean Elab Meta

/-! Exercise the file constructor before public file/section syntax is added. -/

/-- Use the real file parameter policy without reading a file in this fixture. -/
elab "file_parameters " literal:str : term => do
  let text := literal.getString
  let source : SqlFileSource := ⟨"fixture", ".", "sql/queries.sql", text⟩
  let .ok items ← (translateText text : IO _) | throwError "fixture SQL failed to translate"
  fileScriptTerm literal source items

/-- The file's dollar parameter stays an argument beside a same-named Lean local. -/
def explicitDollar (x : Value) := file_parameters "SELECT $x, ?3, :tail; SELECT $x"

example (ignored x gap tail : Value) : explicitDollar ignored x gap tail =
    (sql "SELECT $x, ?3, :tail; SELECT $x") gap tail := rfl

/-- Repeated names across statements retain one argument and the original parameter numbers. -/
def repeated := file_parameters "SELECT :x, :x, ?3; SELECT :x"

example (x gap : Value) : repeated x gap = (sql "SELECT :x, :x, ?3; SELECT :x") x gap := rfl

/-- Files without parameters construct precisely the same ordinary script. -/
def constantFile := file_parameters "SELECT 1 + 2"

example : constantFile = sql "SELECT 1 + 2" := rfl

/-- Unicode diagnostics use character columns, while parser positions are UTF-8 bytes. -/
def diagnosticSource : SqlFileSource :=
  ⟨"fixture", ".", "sql/queries.sql", "-- header\r\nSELECT 'é😀', :x, @x"⟩

#guard diagnosticSource.diagnostic
  { start := "-- header\r\nSELECT 'é😀', :x, ".utf8ByteSize, stop := 0, message := "collision" }
  (some "query") = "sql/queries.sql:2:18: in statement `query`: collision"

/-- Original dollar spellings survive recovery and actual-value replay validation. -/
elab "check_file_source" : command => Command.liftTermElabM do
  let expression := mkAppN (mkConst ``explicitDollar)
    #[toExpr (Value.integer 99), toExpr (Value.integer 1), toExpr (Value.integer 2), toExpr (Value.integer 3)]
  let source ← Replay.scriptText expression
  unless source.text == "SELECT $x, ?3, :tail; SELECT $x" do
    throwError "file source text changed"
  unless source.value.statements.map (·.2) == [[.integer 1, .null, .integer 2, .integer 3], [.integer 1]] do
    throwError "file parameter identities changed"
  unless (← sourceOf scriptSourceKey expression).any (fun source => !source.fileName.isEmpty) do
    throwError "file construction lost its Lean source location"
  logInfo "file construction and replay passed"

check_file_source
