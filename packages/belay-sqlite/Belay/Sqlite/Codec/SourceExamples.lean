import Belay.Sqlite.Codec.Source

set_option doc.verso true

/-! Checks of {name}`Belay.Sqlite.schemaInputsSource`,
{name}`Belay.Sqlite.sqlInputsSource` and the script record, run when the codec
builds. Both generated modules of a sample that uses every kind of value are
elaborated as Lean commands, and the compiled evaluator compares each declaration
with the value. A JSON round trip checks the record. -/

namespace Belay.Sqlite.Codec.SourceExamples

open Lean Elab Command Belay.Sqlite

/-- A column definition with a type and constraints. -/
def column (name : Identifier) (declaredType : Option String) (constraints : List Syntax.ColumnConstraint := []) :
    Syntax.ColumnDefinition :=
  { name, declaredType, constraints }

/-- A schema and a script whose values use names with quotes and non-ASCII letters, a name
that matches only after ASCII folding, negative integers, text and blob bytes, a
default, keys, an index and a prepare error. -/
def sampleRecord : ScriptRecord where
  version := 4
  release := "3.51.0"
  sourceId := "2025-11-04 19:38:17 fb2c931ae597f8d00a37574ff67aeed3eced4e5547f9120744ae4bfa8e74527b"
  schema := [.createTable (name! "Ünit \"q\"") [column (name! "id") (some "BIGINT") [.primaryKey false],
      column (name! "at") (some "TIMESTAMP") [.default (.currentTime "CURRENT_TIMESTAMP") "CURRENT_TIMESTAMP"], column (name! "b") none]
      [.unique [(name! "b")]], .createIndex (name! "by_at") true (name! "Ünit \"q\"")
        [{ expression := .identifier (name! "at") .none, descending := true }] (some (.isNull (.identifier (name! "b") .none) true))]
  script := [.begin, .addColumn (name! "ÜNIT \"Q\"") (column (name! "n") (some "TEXT")),
    .insert (name! "Ünit \"q\"") (some [(name! "id"), (name! "at"), (name! "b"), (name! "n")]) [[.negate (.numeric "9"), .null, .null, .blob [0, 255]]] [],
    .update (name! "Ünit \"q\"") [((name! "n"), .string [104, 105])] (some (.compare .eq (.identifier (name! "id") .none) (.numeric "0x10"))),
    .insert (name! "missing") none [[.null]] [], .commit]

/-- The resolved sample, or nothing when it does not resolve. -/
def sample : Option ResolvedScript := sampleRecord.resolve.toOption

#guard sample.isSome

#guard (decodeScriptRecord (toJson sampleRecord)).toOption.map (·.script) == some sampleRecord.script

#guard (decodeScriptRecord (toJson { sampleRecord with version := 1 })) matches .error _
#guard (decodeScriptRecord (toJson { sampleRecord with version := 2 })) matches .error _

/-- Elaborate the commands of a generated module after its {lit}`import` lines, and
stop at the first parse or elaboration error with Lean's messages. -/
def elaborateModule (name source : String) : CommandElabM Unit := do
  let body := "\n".intercalate ((source.splitOn "\n").filter (!·.startsWith "import "))
  let input := Parser.mkInputContext body s!"<generated {name}>"
  let advice := "fix the source printer in Belay/Sqlite/Codec/Source.lean"
  let mut state : Parser.ModuleParserState := {}
  repeat
    let (command, next, messages) := Parser.parseCommand input { env := ← getEnv, options := {} } state {}
    if messages.hasErrors then
      let texts ← messages.toList.mapM (·.toString)
      throwError "generated module {name} does not parse; {advice}:\n{"\n".intercalate texts}"
    if Parser.isTerminalCommand command then break
    elabCommand command
    if (← get).messages.hasErrors then
      let texts ← (← get).messages.toList.mapM (·.toString)
      throwError "generated module {name} does not elaborate; {advice}:\n{"\n".intercalate texts}"
    state := next

/-- The error text of elaborating a module, or the empty text when it succeeds. The
command state is restored afterwards, so the messages of a failure stay out of
this file's result. -/
def elaborationError (name source : String) : CommandElabM String := do
  let saved ← get
  let text ← try
      elaborateModule name source
      pure ""
    catch error => error.toMessageData.toString
  set saved
  return text

-- A module that does not parse, and one that does not elaborate, name the module,
-- keep Lean's diagnostic and say what to fix.
run_cmd do
  let parse ← elaborationError "BrokenSyntax" "import SqliteVerifier\ndef broken : Nat := ("
  let elaboration ← elaborationError "BrokenType" "def broken : Nat := \"text\""
  unless parse.contains "generated module BrokenSyntax does not parse" && parse.contains "unexpected end of input" &&
      parse.contains "fix the source printer" do
    throwError "elaborateModule gave an unexpected parse diagnostic; make it name the module, keep Lean's message and give the fix:\n{parse}"
  unless elaboration.contains "generated module BrokenType does not elaborate" &&
      elaboration.contains "Type mismatch" && elaboration.contains "fix the source printer" do
    throwError "elaborateModule gave an unexpected elaboration diagnostic; make it name the module, keep Lean's message and give the fix:\n{elaboration}"

run_cmd do
  let some resolution := sample | throwError "the sample does not resolve"
  elaborateModule "SchemaInputs" (schemaInputsSource resolution)
  elaborateModule "SqlInputs" (sqlInputsSource resolution)

#guard sample.map (·.profile) == some Generated.profile
#guard sample.map (·.schema) == some Generated.schema
#guard sample.map (·.startCatalog) == some Generated.startCatalog
#guard sample.map (·.script) == some Generated.script
#guard sample.map (·.resolved) == some Generated.resolved
#guard sample.map (·.nextCatalog) == some Generated.nextCatalog

-- A prepare error has SQLite's message and one flat JSON form, whether it names a catalog
-- object or not.
#guard (PrepareError.noSuchTable (name! "t")).message == "no such table: t"
#guard (PrepareError.expression (.noSuchColumn (name! "a"))).message == "no such column: a"
#guard (PrepareError.expression (.valueCount (name! "t") 2 3)).message == "table t has 2 columns but 3 values were supplied"
#guard (toJson (PrepareError.noSuchTable (name! "t"))).compress == "{\"noSuchTable\":{\"name\":\"t\"}}"
#guard (toJson (PrepareError.expression (.noSuchColumn (name! "a")))).compress == "{\"noSuchColumn\":{\"name\":\"a\"}}"
#guard (toJson (PrepareError.expression .valuesDiffer)).compress == "\"valuesDiffer\""

end Belay.Sqlite.Codec.SourceExamples
