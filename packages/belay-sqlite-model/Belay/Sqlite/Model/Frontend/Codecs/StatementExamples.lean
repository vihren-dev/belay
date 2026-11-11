import Belay.Sqlite.Model.Frontend.Codecs.Resolution

set_option doc.verso true

namespace Belay.Sqlite.Model.Codec.StatementExamples

/-- Decode a statement from JSON text. -/
def decoded (text : String) : Except String Syntax.Statement :=
  Lean.Json.parse text >>= Lean.fromJson?

#guard match decoded "{\"delete\": {\"table\": \"t\", \"filter\": null, \"returning\": []}}" with
  | .ok statement => statement == .delete (Identifier.ofString "t") none [] []
  | .error _ => false

#guard match decoded "{\"select\": null}" with
  | .error _ => true
  | .ok _ => false

end Belay.Sqlite.Model.Codec.StatementExamples
