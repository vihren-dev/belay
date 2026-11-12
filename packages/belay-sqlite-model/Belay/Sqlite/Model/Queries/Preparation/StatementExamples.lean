import Belay.Sqlite.Model.Queries.Preparation.Resolution

set_option doc.verso true

/-! Checked examples of the JSON of statements (ADR 0018, D1): a statement without
subqueries has no {lit}`subqueries` field, in both directions, and a malformed payload is a
decoding error, not a panic. -/

namespace Belay.Sqlite.Model.Codec.StatementExamples

#guard (Lean.toJson (Syntax.Statement.delete (Identifier.ofString "t") none [] [])).compress ==
  "{\"delete\":{\"filter\":null,\"returning\":[],\"table\":\"t\"}}"

end Belay.Sqlite.Model.Codec.StatementExamples
