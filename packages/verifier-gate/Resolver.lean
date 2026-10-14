import Belay.Sqlite.Codec.Source

/-! `migration-resolver RECORD OUTPUT_DIR`: resolve the frontend's structural record
and write the generated input modules as Lean source. When the record resolves,
it writes `SchemaInputs.lean` and `SqlInputs.lean` into the output directory. It
writes one JSON object on standard output:

* `{"status": "resolved"}`;
* `{"status": "restricted", "part": "schema" | "script", "statement": N, "path": [...], "reason": TEXT}`;
* `{"status": "schemaError", "statement": N, "message": TEXT}` for a schema statement
  that SQLite refuses to prepare.

The gates do not trust this output: they resolve the record again. See ADR 0008,
"Where resolution runs". -/

open Lean Belay.Sqlite

/-- The JSON of a model restriction in the schema or the script, with its message and its
stable id. -/
def restrictionJson (part : String) (restriction : Restriction) : Json :=
  Json.mkObj [("status", "restricted"), ("part", toJson part), ("statement", toJson restriction.statement),
    ("path", toJson restriction.path), ("reason", toJson restriction.reason),
    ("restriction", toJson restriction.kind.id)]

/-- The JSON status of an issue: a restriction or a schema prepare error. -/
def issueJson : ScriptIssue → Json
  | .schemaRestricted restriction => restrictionJson "schema" restriction
  | .scriptRestricted restriction => restrictionJson "script" restriction
  | .schemaPrepareError statement error => Json.mkObj [("status", "schemaError"),
      ("statement", toJson statement), ("message", toJson error.message)]

/-- Exit 0 with a status for every decodable record, and 1 for an unreadable record
or a wrong command line. -/
def main (arguments : List String) : IO UInt32 := do
  let [record, output] := arguments
    | IO.eprintln "usage: migration-resolver SCRIPT_RECORD_JSON OUTPUT_DIR"; return 1
  match Json.parse (← IO.FS.readFile record) >>= decodeScriptRecord with
  | .error message =>
    IO.eprintln s!"migration-resolver: unreadable script record: {message}; prepare the inputs again"
    return 1
  | .ok decoded =>
    match decoded.resolve with
    | .ok resolution =>
      IO.FS.writeFile (System.FilePath.mk output / "SchemaInputs.lean") (schemaInputsSource resolution)
      IO.FS.writeFile (System.FilePath.mk output / "SqlInputs.lean") (sqlInputsSource resolution)
      IO.println (Json.mkObj [("status", "resolved")]).compress
    | .error issue => IO.println (issueJson issue).compress
    return 0
