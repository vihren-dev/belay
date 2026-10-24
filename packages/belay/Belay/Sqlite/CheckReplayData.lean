import Belay.Sqlite.CheckData
import Belay.Sqlite.ReplayScript
import Belay.Sqlite.ProgramQueries

set_option doc.verso true

/-! Replay preparation for background checking. Data evaluation and model execution use
cooperative reduction. Native translation receives bounded text; explicit replay APIs remain
available for larger scripts and databases. -/

namespace Belay.Sqlite.Check

open Lean Meta Elab Term

-- These instances reify only data returned by the existing model observation function.
deriving instance Lean.ToExpr for Belay.Sqlite.Model.Output
deriving instance Lean.ToExpr for Except

/-- Whether construction succeeds without a model restriction or open transaction and yields
exactly the requested raw database. Every step comes from the ordinary model runner. -/
def constructionMatches (statements : List Model.Syntax.Statement) (database : Database.Raw) : Bool :=
  let run := Database.Raw.run {} ⟨statements.map (·, [])⟩
  Belay.Sqlite.List.allOk run.outputs && run.connection.state.snapshot.isNone && run.connection.state.database == database

/-- Bound native parser/formatter input in the automatic path. Large original texts remain
available to explicit replay; this finite heuristic limit gives no logical conclusion. -/
private def checkTextSize (text : String) : TermElabM Unit := do
  if text.utf8ByteSize > maxReplayBytes then throwError "SQL checking reached its replay text limit"
  checkSystem "SQL replay text"

/-- Reconstruct a database with original metadata or the existing ordinary-table formatter.
The shared formatter receives only checked literal database data and checks resources between
table/row fragments. Its text is an untrusted proposal. The model execution that validates
the exact reconstruction is reduced under the checking budget. -/
def checkedConstruction (expression : Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM String := do
  let database ← databaseValue expression excluded excludedLocals
  let source ← sourceOf databaseSourceKey expression
  let text ← match source with
    | some source => pure (some source.text)
    | none =>
      let bytes ← IO.mkRef (0 : Nat)
      Replay.databaseSqlWith (fun fragment => do
        checkSystem "SQL replay formatting"
        bytes.modify (· + fragment.utf8ByteSize)
        if (← bytes.get) > maxReplayBytes then throwError "SQL checking reached its replay text limit") database
  let some text := text | throwError "no SQL construction is available for this database"
  checkTextSize text
  let .ok items ← (Replay.translated text : IO _)
    | throwError "database construction cannot be translated"
  checkSystem "SQL replay translation"
  if items.any (fun item => !item.parameters.isEmpty) then
    throwError "database construction has unbound parameters"
  let reconstructed ← dataValue Bool (mkApp2 (mkConst ``constructionMatches)
    (toExpr (items.toList.map (·.statement.value))) (toExpr database.raw)) excluded excludedLocals
  unless reconstructed do throwError "database construction does not reproduce this witness successfully"
  return text

/-- Prepare the same original-query report as explicit replay, using cooperative evaluation
for the database, script and model observations. Missing source or opaque computation makes
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
  let observed ← dataValue (Except String (List Output))
    (mkApp2 (mkConst ``Replay.observations) database script) excluded excludedLocals
  let .ok outputs := observed | throwError "SQL replay has an unavailable observation"
  Replay.render construction source outputs

end Belay.Sqlite.Check
