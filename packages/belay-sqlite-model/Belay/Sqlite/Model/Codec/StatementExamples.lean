import Belay.Sqlite.Model.Codec.Resolution

set_option doc.verso true

/-! Checked examples of the JSON of statements (ADR 0018, D1): a statement without
subqueries has no {lit}`subqueries` field, in both directions, and a malformed payload is a
decoding error, not a panic. -/

namespace Belay.Sqlite.Model.Codec.StatementExamples

/-- Decode a statement from JSON text. -/
def decoded (text : String) : Except String Syntax.Statement :=
  Lean.Json.parse text >>= Lean.fromJson?

#guard match decoded "{\"delete\": {\"table\": \"t\", \"filter\": null, \"returning\": []}}" with
  | .ok statement => statement == .delete (Identifier.ofString "t") none [] []
  | .error _ => false
#guard (Lean.toJson (Syntax.Statement.delete (Identifier.ofString "t") none [] [])).compress ==
  "{\"delete\":{\"filter\":null,\"returning\":[],\"table\":\"t\"}}"
#guard match decoded "{\"select\": null}" with
  | .error _ => true
  | .ok _ => false

end Belay.Sqlite.Model.Codec.StatementExamples
