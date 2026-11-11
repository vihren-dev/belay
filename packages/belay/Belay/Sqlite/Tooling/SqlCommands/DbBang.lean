import Belay.Sqlite.Tooling.SqlCommands.SqlEditorInfo
import Belay.Sqlite.Frontend.Embedding.DbBang
import Belay.Sqlite.Schema.Rows.DbBang

set_option doc.verso true

/-! {lit}`db! r"..."`: the database that the SQL text builds on the empty database while the file
elaborates. Each statement that fails, and the statement that ends the run, is an elaboration
error at its position in the text. The term holds the database as a literal and the decision of
{lit}`Database.Valid` for it, which the kernel checks. -/

namespace Belay.Sqlite

open Lean Elab Term Meta

/-- Elaborate {lit}`db! "SQL"`: translate the text, give an error at each parameter
({name}`parameterDiagnostic`), or else run the text on the empty database and log each error
of {name}`runDiagnostics` at its range of the text ({name}`textRange`). After an error, the term
is a {lit}`sorry` that Lean shows no second error for. Otherwise the term is
{name}`databaseTerm` of the database, and its error is an error at the literal. A successful value retains its source text as
replay metadata, which replay consumers validate against the actual database. It also records, for the
declaration that holds the term, where each table of the final catalog is created
({name}`registerTableOrigins`), outside the value, and gives the table names editor information with the
rows that the run reached ({name}`executedContexts`) and warns about a statement with several permitted
results or an {lit}`INSERT ... SELECT` that depends on an order ({name}`orderRunWarnings`). When the text has an error, the names still get their
information up to the statement that failed, so that an unknown name gets its corrections. -/
@[term_elab dbBangTerm]
def elabDbBang : TermElab := fun term _ => do
  let literal := term[1]
  let some text := literal.isStrLit? | throwUnsupportedSyntax
  let items ← literalStatements literal
  let statements := items.toList.map (·.statement)
  let parameters := items.toList.flatMap (·.parameters)
  let (diagnostics, connection) := if parameters.isEmpty then runDiagnostics text.toUTF8 statements
    else (parameters.map parameterDiagnostic, Database.empty.raw.connection)
  for diagnostic in diagnostics do
    logErrorAt (textRange literal text diagnostic.start diagnostic.stop) diagnostic.message
  let (contexts, outputs) := executedContexts 0 Database.empty.raw.connection statements
  if !diagnostics.isEmpty then
    if parameters.isEmpty then emitSqlEditorInfo (.literal literal text) statements {} contexts
    return ← mkLabeledSorry (mkConst ``Database) (synthetic := true) (unique := false)
  match databaseTerm connection.state.database with
  | .error message => throwErrorAt literal message
  | .ok database =>
    registerTableOrigins (.literal literal text) statements connection.state.database.catalog database
    emitSqlEditorInfo (.literal literal text) statements {} contexts
    logOrderWarnings literal text (orderRunWarnings statements outputs)
    return withSource databaseSourceKey literal text (← getFileName) database

end Belay.Sqlite
