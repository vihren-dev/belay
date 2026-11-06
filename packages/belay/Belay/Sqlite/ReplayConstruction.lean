import Belay.Sqlite.ReplayDatabaseSql
import Belay.Sqlite.ReplayEvaluation
import Belay.Sqlite.DbBang

set_option doc.verso true

/-! Validate replay construction against the supplied witness. Original db! text can retain
constraints that the simple schema formatter cannot express. Both paths must reconstruct the
same catalog, rowids and cells through the existing model runner. -/

namespace Belay.Sqlite.Replay

open Lean Elab Term Meta

/-- Translate text for replay, retaining statement ranges and parameter tokens. Translation
refusal is an unavailable replay, rather than an alleged native SQLite error. -/
def translated (text : String) : IO (Except String (Array Translation.ParameterizedStatement)) := do
  return (← translateText text).mapError (fun refusal => refusal.message)

/-- The INSERT statements of the rows that the database has in the table of this name. None
when the catalog has no table of the name or a row has no SQL spelling. -/
private def tableRowsSql (database : Database) (name : Model.Identifier) : Option String := do
  let some (object, position) := database.raw.catalog.zipIdx.find? (·.1.name.sameName name)
    | none
  let .table table := object.entry | none
  let rows ← (database.raw.rows.getD position []).mapM (rowSql object.name table)
  return String.join rows

/-- Construction text for a database whose catalog comes from SQL text, for example a
candidate that the checker generated on the schema of a {lit}`db!` constant. The text keeps
the schema's statements in their order, leaves out its INSERT statements, and inserts the
database's rows of each table right after the statement that creates the table. So the rows
are stored before any trigger or index that a later statement creates, and no trigger fires.
None when the text has another statement kind, such as an ALTER TABLE or an UPDATE. The text
is a proposal: the caller validates that it builds exactly the database. -/
def schemaRowsSql (schema : String) (database : Database) : IO (Option String) := do
  let .ok items ← translated schema | return none
  let bytes := schema.toUTF8
  let mut fragments := #[]
  for item in items do
    let span := item.statement.span
    let some text := String.fromUTF8? (bytes.extract span.start span.stop) | return none
    match item.statement.value with
    | .insert .. => continue
    | .createTable name .. =>
      let some rows := tableRowsSql database name | return none
      fragments := fragments.push (text ++ ";\n" ++ rows)
    | .createIndex .. | .createView .. | .createTrigger .. =>
      fragments := fragments.push (text ++ ";\n")
    | .addColumn .. | .renameTable .. | .renameColumn .. | .dropColumn .. | .dropTable .. | .dropView ..
    | .dropIndex .. | .dropTrigger .. | .begin | .commit | .rollback | .insertSelect .. | .update ..
    | .delete .. | .select .. | .pragma .. => return none
  return some (String.join fragments.toList)

/-- Check that construction text builds precisely the supplied database, with no parameters,
errors, model restrictions or open transaction. A different catalog or cell fails validation. -/
def validateConstruction (text : String) (database : Database) : IO (Except String Unit) := do
  let .ok items ← translated text | return .error "database construction cannot be translated"
  if items.any (fun item => !item.parameters.isEmpty) then
    return .error "database construction has unbound parameters"
  let (diagnostics, connection) := runDiagnostics text.toUTF8 (items.toList.map (·.statement))
  if !diagnostics.isEmpty then return .error "database construction has an error or unavailable observation"
  if connection.state.database != database.raw then
    return .error "database construction does not reproduce the witness"
  return .ok ()

/-- Obtain checked database data and validated construction text. An explicit text is the
flexible primitive; otherwise use original db! metadata or the ordinary-table formatter.
Unsupported reconstruction fails without replacing the witness with another database. -/
def construction (expression : Expr) (text : Option String := none)
    (excluded : Array Name := #[]) (excludedLocals : Array FVarId := #[]) :
    TermElabM (Database × String) := do
  let database ← databaseValue expression excluded excludedLocals
  let source ← sourceOf databaseSourceKey expression
  let some text := text.or (source.map (·.text)) |>.or (databaseSql database)
    | throwError "no SQL construction is available for this database; supply its construction text"
  match ← (validateConstruction text database : IO _) with
  | .error reason => throwError "{reason}; supply SQL that builds this exact database"
  | .ok () => return (database, text)

end Belay.Sqlite.Replay
