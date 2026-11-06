import Belay.Sqlite.CheckData
import Belay.Sqlite.ReplayScript
import Belay.Sqlite.ProgramQueries

set_option doc.verso true

/-! Replay preparation for background checking. Data evaluation and model execution use
compiled code within the time limit of the check, and the kernel checks each value. Native translation receives bounded text; explicit replay APIs remain
available for larger scripts and databases. -/

namespace Belay.Sqlite.Check

open Lean Meta Elab Term

/-- Whether construction succeeds without a model restriction or open transaction and yields
exactly the requested raw database. Every step comes from the ordinary model runner. -/
def constructionMatches (statements : List Model.Syntax.Statement) (database : Database.Raw) : Bool :=
  let run := Database.Raw.run {} ⟨statements.map (·, [])⟩
  Belay.Sqlite.List.allOk run.outputs && run.connection.state.snapshot.isNone && run.connection.state.database == database

/-- The database without its triggers: the catalog without the trigger objects, and the rows of
the other objects. -/
def withoutTriggers (database : Database.Raw) : Database.Raw :=
  let kept := database.catalog.zipIdx.filter fun (object, _) => !(object.entry matches .trigger _)
  { catalog := kept.map (·.1), rows := kept.map fun (_, position) => database.rows.getD position [] }

/-- The rows of a database without triggers ({name}`withoutTriggers`) placed back in the catalog
with the triggers: a trigger gets no rows, each other object the next rows in order. -/
def rowsWithTriggers (catalog : Catalog) (rows : List (List Model.Row)) : List (List Model.Row) :=
  match catalog with
  | [] => []
  | object :: objects =>
    if object.entry matches .trigger _ then [] :: rowsWithTriggers objects rows
    else rows.headD [] :: rowsWithTriggers objects rows.tail

/-- Whether the schema statements, then the row statements on the result without its triggers,
succeed without a model restriction or open transaction, keep the catalog, and give exactly the
requested raw database once the triggers are back. This is how SQLite runs a construction whose
rows are inserted with {lit}`.dbconfig enable_trigger off`
({name}`Replay.SchemaConstruction.triggersOff`). -/
def constructionWithoutTriggersMatches (schema rows : List Model.Syntax.Statement) (database : Database.Raw) : Bool :=
  let first := Database.Raw.run {} ⟨schema.map (·, [])⟩
  let built := first.connection.state.database
  let bare := withoutTriggers built
  let second := bare.run ⟨rows.map (·, [])⟩
  let filled := second.connection.state.database
  Belay.Sqlite.List.allOk first.outputs && first.connection.state.snapshot.isNone &&
    Belay.Sqlite.List.allOk second.outputs && second.connection.state.snapshot.isNone &&
    filled.catalog == bare.catalog &&
    ({ built with rows := rowsWithTriggers built.catalog filled.rows } : Database.Raw) == database

/-- Bound native parser/formatter input in the automatic path. Large original texts remain
available to explicit replay; this finite heuristic limit gives no logical conclusion. -/
private def checkTextSize (text : String) : TermElabM Unit := do
  if text.utf8ByteSize > maxReplayBytes then throwError "SQL checking reached its replay text limit"
  checkSystem "SQL replay text"

/-- The statements of construction text, after the size and parameter checks. -/
private def constructionStatements (text : String) : TermElabM (List Model.Syntax.Statement) := do
  checkTextSize text
  let .ok items ← (Replay.translated text : IO _)
    | throwError "database construction cannot be translated"
  checkSystem "SQL replay translation"
  if items.any (fun item => !item.parameters.isEmpty) then
    throwError "database construction has unbound parameters"
  return items.toList.map (·.statement.value)

/-- Reconstruct a database with original metadata, with the schema text of a generated
database ({name}`Replay.schemaRowsSql`), or with the existing ordinary-table formatter.
The shared formatter receives only checked literal database data and checks resources between
table/row fragments. Its text is an untrusted proposal. Compiled model execution validates the
exact reconstruction ({name}`constructionMatches`, {name}`constructionWithoutTriggersMatches`). -/
def checkedConstruction (expression : Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM String := do
  let database ← databaseValue expression excluded excludedLocals
  let source ← sourceOf databaseSourceKey expression
  let fromSchema ← match ← sourceOf schemaSourceKey expression with
    | some schema =>
      checkTextSize schema.text
      (Replay.schemaRowsSql schema.text database : IO _)
    | none => pure none
  let validated (matching : Expr) : TermElabM Unit := do
    unless ← dataValue Bool matching excluded excludedLocals do
      throwError "database construction does not reproduce this witness successfully"
  if source.isNone then
    if let some (.triggersOff schema rows) := fromSchema then
      validated (mkApp3 (mkConst ``constructionWithoutTriggersMatches)
        (toExpr (← constructionStatements schema)) (toExpr (← constructionStatements rows)) (toExpr database.raw))
      return (Replay.SchemaConstruction.triggersOff schema rows).text
  let text ← match source, fromSchema with
    | some source, _ => pure (some source.text)
    | none, some construction => pure (some construction.text)
    | none, none =>
      let bytes ← IO.mkRef (0 : Nat)
      Replay.databaseSqlWith (fun fragment => do
        checkSystem "SQL replay formatting"
        bytes.modify (· + fragment.utf8ByteSize)
        if (← bytes.get) > maxReplayBytes then throwError "SQL checking reached its replay text limit") database
  let some text := text | throwError "no SQL construction is available for this database"
  validated (mkApp2 (mkConst ``constructionMatches)
    (toExpr (← constructionStatements text)) (toExpr database.raw))
  return text

/-- Reify outputs as terms. This is a plain value and no global instance, because exported
{name}`ToExpr` instances override the display of a user's {lit}`#eval`. Bring it into scope with
{lit}`let _ := outputExprInstance` where observation data is decoded. -/
@[instance_reducible] def outputExprInstance : ToExpr Output where
  toTypeExpr := mkConst ``Model.Output
  toExpr := fun
    | .rows rows => mkApp (mkConst ``Model.Output.rows) (toExpr rows)
    | .done changes => mkApp (mkConst ``Model.Output.done) (toExpr changes)
    | .error code => mkApp (mkConst ``Model.Output.error) (toExpr code)
    | .oneOf results => mkApp (mkConst ``Model.Output.oneOf) (toExpr results)
    | .unmodeled reason => mkApp (mkConst ``Model.Output.unmodeled) (toExpr reason)

/-- Prepare the same original-query report as explicit replay, using compiled evaluation
({name}`dataValue`) for the database, script and model observations. Missing source or opaque computation makes
this background attempt unavailable, without changing the explicit certification primitive. -/
def checkedScriptReport (database script : Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM Replay.Report := do
  let construction ← checkedConstruction database excluded excludedLocals
  let value ← scriptValue script excluded excludedLocals
  let some original ← sourceOf scriptSourceKey script
    | throwError "no original SQL is available for this script"
  checkTextSize original.text
  let source ← Replay.scriptTextOf script value (some original.text)
  checkSystem "SQL replay translation"
  let _ := outputExprInstance
  let errorType := toTypeExpr String
  let resultType := toTypeExpr (List Output)
  let _ : ToExpr (Except String (List Output)) := {
    toTypeExpr := mkApp2 (mkConst ``Except [.zero, .zero]) errorType resultType
    toExpr := fun
      | .ok outputs => mkApp3 (mkConst ``Except.ok [.zero, .zero]) errorType resultType (toExpr outputs)
      | .error reason => mkApp3 (mkConst ``Except.error [.zero, .zero]) errorType resultType (toExpr reason) }
  let observed ← dataValue (Except String (List Output))
    (mkApp2 (mkConst ``Replay.observations) database script) excluded excludedLocals
  let .ok outputs := observed | throwError "SQL replay has an unavailable observation"
  Replay.render construction source outputs

end Belay.Sqlite.Check
