import Belay.Sqlite.Tooling.Counterexamples.ReplayDatabaseSql
import Belay.Sqlite.Tooling.Counterexamples.ReplayEvaluation
import Belay.Sqlite.Tooling.SqlCommands.DbBang
import Belay.Sqlite.Tooling.Counterexamples.SqlSource

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

/-- The construction of a database on the catalog of a schema text ({lit}`schemaRowsSql`). -/
inductive SchemaConstruction where
  /-- One text: the schema's statements, with each table's rows right after the statement that
  creates the table. -/
  | inline (text : String)
  /-- The schema's statements without their INSERTs, then the rows of every table, which the
  replay inserts with the triggers off. -/
  | triggersOff (schema rows : String)
  deriving Inhabited

/-- The replay text of a construction. For {name}`SchemaConstruction.triggersOff`, the SQLite
shell commands {lit}`.dbconfig enable_trigger off` and {lit}`on` enclose the rows, so that no
trigger fires while they are inserted. -/
def SchemaConstruction.text : SchemaConstruction → String
  | .inline text => text
  | .triggersOff schema rows =>
    schema ++ ".dbconfig enable_trigger off\n" ++ rows ++ ".dbconfig enable_trigger on\n"

/-- The construction of a database whose catalog comes from SQL text, for example a candidate
that the checker generated on the schema of a {lit}`db!` constant. The INSERT statements of the
text are left out; the database's rows replace them. When the text has only CREATE and INSERT
statements, the rows of each table follow the statement that creates the table, so they are
stored before any trigger or index that a later statement creates, and no trigger fires
({name}`SchemaConstruction.inline`). Otherwise, for example with an ALTER TABLE, the text's other
statements come first, then the rows of every table with the triggers off
({name}`SchemaConstruction.triggersOff`). None when the text has a PRAGMA, which can change the
connection that inserts the rows, or a row has no SQL spelling. The construction is a proposal:
the caller validates that it builds exactly the database. -/
def schemaRowsSql (schema : String) (database : Database) : IO (Option SchemaConstruction) := do
  let .ok items ← translated schema | return none
  let bytes := schema.toUTF8
  let mut inline := some #[]
  let mut statements := #[]
  for item in items do
    let span := item.statement.span
    let some text := String.fromUTF8? (bytes.extract span.start span.stop) | return none
    match item.statement.value with
    | .insert .. | .insertSelect .. => continue
    | .pragma .. => return none
    | .createTable name .. =>
      inline := inline.bind fun fragments => (tableRowsSql database name).map (fragments.push <| text ++ ";\n" ++ ·)
      statements := statements.push (text ++ ";\n")
    | .createIndex .. | .createView .. | .createTrigger .. =>
      inline := inline.map (·.push (text ++ ";\n"))
      statements := statements.push (text ++ ";\n")
    | .addColumn .. | .renameTable .. | .renameColumn .. | .dropColumn .. | .dropTable .. | .dropView ..
    | .dropIndex .. | .dropTrigger .. | .begin | .commit | .rollback | .update .. | .delete .. | .select .. =>
      inline := none
      statements := statements.push (text ++ ";\n")
  if let some fragments := inline then return some (.inline (String.join fragments.toList))
  let tables := database.raw.catalog.filter fun object => object.entry matches .table _
  let some rows := tables.mapM (tableRowsSql database ·.name) | return none
  return some (.triggersOff (String.join statements.toList) (String.join rows))

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
