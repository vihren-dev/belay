import Belay.Sqlite.Tooling.Counterexamples.EvalDatabase
import Belay.Sqlite.Schema.Dispatch.SqlEditorInfo
import Belay.Sqlite.Tooling.SqlCommands.SqlEditorInfo
import Belay.Sqlite.Frontend.Embedding.SqlBang

set_option doc.verso true

/-! {lit}`sql! db r"..."`: the script of {lit}`sql r"..."`, which also resolves its statements
against the catalog of the database {lit}`db` while the file elaborates, as {lit}`db.run` does
when it starts. Each prepare error, such as {lit}`no such column: nmae`, and the first model
restriction are elaboration errors at the name or node in the SQL text. -/

namespace Belay.Sqlite

open Lean Elab Term

/-- Elaborate {lit}`sql! db "SQL"`: translate the text, evaluate {lit}`db`
({name}`evaluateDatabase`), log each error of {name}`scriptDiagnostics` at its range of the text
({name}`textRange`), give the table names editor information ({name}`emitSqlEditorInfo`, with the origins
of the database term, {name}`KnownDatabase.ofTerm`), and give the
term of {lit}`sql "SQL"` ({name}`scriptTerm`). When {lit}`db` has an error, which Lean already shows, it
gives the script without the check. -/
@[term_elab sqlBangTerm]
def elabSqlBang : TermElab := fun term _ => do
  let literal := term[2]
  let some text := literal.isStrLit? | throwUnsupportedSyntax
  let items ← literalStatements literal
  if let some evaluated ← evaluateDatabase term[1] then
    let statements := items.toList.map (·.statement)
    let connection := evaluated.value.raw.connection
    for diagnostic in scriptDiagnostics connection.resolveState text.toUTF8 statements do
      logErrorAt (textRange literal text diagnostic.start diagnostic.stop) diagnostic.message
    emitSqlEditorInfo (.literal literal text) statements (.ofTerm (← getEnv) evaluated.term)
      (resolvedContexts connection.resolveState (some connection.state.database.rows) statements)
  scriptTerm literal text items

end Belay.Sqlite
