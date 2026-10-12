import Belay.Sqlite.Codec.Source

set_option doc.verso true

/-! Checks of {name}`Belay.Sqlite.leanTerm` and the request record, run when the
codec builds. The printed terms of a request that uses every kind of value are
elaborated as Lean source, and the compiled evaluator compares the result with
the value. A JSON round trip checks the record. -/

namespace Belay.Sqlite.Codec.SourceExamples

open Lean Elab Command Belay.Sqlite

/-- A column definition with a type and constraints. -/
def column (name : String) (declaredType : Option String) (constraints : List Syntax.ColumnConstraint := []) :
    Syntax.ColumnDefinition :=
  { name, declaredType, constraints }

/-- A request whose values use names with quotes and non-ASCII letters, a name
that matches only after ASCII folding, negative integers, text and blob bytes, a
default, keys, an index and a prepare error. -/
def sampleRecord : RequestRecord where
  version := 2
  release := "3.51.0"
  sourceId := "2025-11-04 19:38:17 fb2c931ae597f8d00a37574ff67aeed3eced4e5547f9120744ae4bfa8e74527b"
  schema := [.createTable "Ünit \"q\"" [column "id" (some "BIGINT") [.primaryKey false],
      column "at" (some "TIMESTAMP") [.default (.currentTime "CURRENT_TIMESTAMP")], column "b" none]
      [.unique ["b"]], .createIndex "by_at" true "Ünit \"q\"" ["at"]]
  script := [.begin, .addColumn "ÜNIT \"Q\"" (column "n" (some "TEXT")),
    .insert "Ünit \"q\"" (some ["id", "at", "b", "n"]) [[.negate (.numeric "9"), .null, .blob [0, 255], .string [104, 105]]],
    .update "Ünit \"q\"" [("n", .null)] (some (.equals (.identifier "id" false) (.numeric "0x10"))),
    .insert "missing" none [[.null]], .commit]

/-- The resolved sample, or nothing when it does not resolve. -/
def sample : Option ResolvedRequest := sampleRecord.resolve.toOption

#guard sample.isSome

#guard (decodeRequestRecord (toJson sampleRecord)).toOption.map (·.script) == some sampleRecord.script

#guard (decodeRequestRecord (toJson { sampleRecord with version := 1 })) matches .error _

/-- Elaborate {lit}`def name : type := term` from source text and stop on any error. -/
def elaborateDefinition (name type term : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command s!"def {name} : {type} :={term}" with
  | .error message => throwError message
  | .ok syntaxTree => elabCommand syntaxTree

run_cmd do
  let some request := sample | throwError "the sample does not resolve"
  elaborateDefinition "printedProfile" "Profile" (leanTerm request.profile)
  elaborateDefinition "printedSchema" "List Syntax.Statement" (leanTerm request.schema)
  elaborateDefinition "printedStart" "Catalog" (leanTerm request.startCatalog)
  elaborateDefinition "printedScript" "List Syntax.Statement" (leanTerm request.script)
  elaborateDefinition "printedResolved" "List Resolved.Statement" (leanTerm request.resolved)
  elaborateDefinition "printedNext" "Catalog" (leanTerm request.nextCatalog)

#guard sample.map (·.profile) == some printedProfile
#guard sample.map (·.schema) == some printedSchema
#guard sample.map (·.startCatalog) == some printedStart
#guard sample.map (·.script) == some printedScript
#guard sample.map (·.resolved) == some printedResolved
#guard sample.map (·.nextCatalog) == some printedNext

end Belay.Sqlite.Codec.SourceExamples
