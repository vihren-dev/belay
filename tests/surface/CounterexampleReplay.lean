import Belay
import CounterexampleReplaySource

open Belay.Sqlite Lean Elab Meta ReplayFixture

/-! Check replay after source definitions have crossed an olean import boundary. -/

/-- Keep exact model value tags so Python can compare native observations without losing bytes. -/
def outputJson : Output → Json
  | .rows rows => Json.mkObj [("rows", toJson rows)]
  | .done changes => Json.mkObj [("done", toJson changes)]
  | .error code => Json.mkObj [("error", toJson code)]
  | .oneOf results => Json.mkObj [("oneOf", toJson results)]
  | .unmodeled reason => Json.mkObj [("unmodeled", toJson reason)]

/-- Emit the production report, without recreating its SQL in the test harness. -/
def emit (name : String) (report : Replay.Report) : Term.TermElabM Unit := do
  logInfo m!"REPLAY:{(Json.mkObj [("name", toJson name), ("sql", toJson report.sqlite),
    ("construction", toJson report.construction), ("original", toJson report.original),
    ("bindings", toJson report.bindings), ("outputs", toJson (report.outputs.map outputJson))]).compress}"

/-- Reject an invalid replay even when its term or metadata would otherwise evaluate. -/
def rejects (action : Term.TermElabM Unit) : Term.TermElabM Unit := do
  let accepted ← try action; pure true catch _ => pure false
  if accepted then throwError "replay accepted inconsistent or unavailable evidence"

set_option maxHeartbeats 2000000 in
elab "check_replays" : command => Command.liftTermElabM do
  let database := mkConst ``sample
  let expression := mkApp (mkConst ``replayQuery) (toExpr (Value.text "a'b".toUTF8.toList))
  emit "values" (← Replay.scriptReport database expression)
  emit "parameters" (← Replay.scriptReport (mkConst ``Database.empty) (mkConst ``parameters))
  emit "overflow" (← Replay.scriptReport (mkConst ``overflow) (mkConst ``sumQuery))
  emit "unbound" (← Replay.scriptReport (mkConst ``Database.empty) (mkConst ``oneQuery))
  emit "numeric-parameters" (← Replay.scriptReport (mkConst ``Database.empty) (mkConst ``numericParameters))
  emit "numeric-boundaries" (← Replay.scriptReport (mkConst ``Database.empty) (mkConst ``numericBoundaries))
  emit "predicate" (← Replay.databaseReport database)
  let schema := (Sampling.schema [("plain", ["a"])]).getD Database.empty
  let generated := (Sampling.uniform schema [.integer 7]).getD Database.empty
  emit "generated" (← Replay.databaseReport (databaseExpr generated.raw))
  let rebound := mkApp2 (mkConst ``Script.withValues) (mkConst ``parameters)
    (toExpr ([[Value.blob [39], .text [65], .null]] : List (List Value)))
  emit "rebound" (← Replay.scriptReport (mkConst ``Database.empty) rebound)
  let badScript := withSource scriptSourceKey Syntax.missing "SELECT 2" "forged" (mkConst ``oneQuery)
  rejects (discard <| Replay.scriptText badScript)
  let badDatabase := withSource databaseSourceKey Syntax.missing "" "forged" database
  rejects (discard <| Replay.construction badDatabase)
  rejects (discard <| Replay.scriptValue (mkConst ``dishonestScript))
  rejects (discard <| Replay.databaseValue (mkConst ``dishonestDatabase))
  for queryName in [``clockQuery, ``counterQuery, ``unknownQuery, ``missingShellTable, ``boundShellTable, ``shellMetadata] do
    rejects (discard <| Replay.scriptReport (mkConst ``Database.empty) (mkConst queryName))
  unless (Replay.observations Database.empty dropShellTable).isOk do
    throwError "the binding-table DROP interference case must be modeled"
  rejects (discard <| Replay.scriptReport (mkConst ``Database.empty) (mkConst ``dropShellTable))
  unless (← sourceOf scriptSourceKey expression).any (fun source => !source.fileName.isEmpty) do
    throwError "source location was lost"
  logInfo "replay trust and unavailable checks passed"

check_replays
