import Belay
import Belay.Sqlite.SqlDocCheck
import Lean.Elab.DocString

set_option doc.verso true

namespace SqlDocRegistration
open Lean Elab Term Belay.Sqlite

/-- Integration probe for the native raw registration and our execution adapter.
The fixture-only header is intentionally smaller than the public SQL block contract. -/
def probe : Doc.DocCodeBlockExpander := fun code => do
  let some databaseTerm ← Doc.getNamed `db (none : Option Ident)
    | throwErrorAt code "SQL probe requires (db := closedDatabase)"
  let expected ← Doc.getNamed `expected ""
  Doc.done
  let some database ← (evaluateDatabase databaseTerm : TermElabM _)
    | return .code code.getString
  let items ← match ← (translateText code.getString : IO _) with
    | .ok items => pure items
    | .error refusal => throwErrorAt code refusal.message
  if items.any (! ·.parameters.isEmpty) then
    throwErrorAt code "This integration probe accepts SQL without parameters"
  let script : Script := ⟨items.toList.map fun item => (item.statement.value, [])⟩
  match SqlDoc.check database Env.default script (.text expected) with
  | .ok () => return .code code.getString
  | .error failure => throwErrorAt code failure.message

initialize Doc.addBuiltinDocCodeBlock `sql_probe ``probe probe
end SqlDocRegistration
