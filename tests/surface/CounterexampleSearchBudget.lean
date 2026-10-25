import Belay
import Belay.Sqlite.CheckData
import Belay.Sqlite.CheckReplayData

open Lean Elab Term Meta Belay.Sqlite

/-! The background evaluator must reduce computation cooperatively before native decoding.
A compiled override and a costly pure expression exercise that boundary without timing assertions. -/

namespace SearchBudgetFixture

/-- This is a finite but deliberately costly computation in a raw script-data projection. -/
def allocationScript (count : Nat) : Script :=
  ⟨[(.commit, [.integer (Int.ofNat (((List.range count).map (· + 1)).sum))])]⟩

/-- The compiled implementation deliberately returns different statement data. -/
def differentImplementation : Script := ⟨[(.rollback, [])]⟩

/-- A definition's logical meaning remains authoritative even with a different implementation. -/
@[implemented_by differentImplementation]
def originalDefinition : Script := ⟨[(.commit, [])]⟩

/-- Closed opaque computations cannot be reduced to literal data by the background checker. -/
opaque opaqueScript : Script := ⟨[(.commit, [])]⟩

/-- A schema that cannot be normalized must not delay an accepted earlier candidate. -/
opaque deferredSchema : Database := Database.empty

/-- SQL values include UInt8/UInt64 constructor data, not only natural-number literals. -/
def bytesAndReal : Script :=
  ⟨[(.commit, [.blob [0, 255], .text [97, 0, 39], .real 0x3ff8000000000000])]⟩

/-- These operations use the existing model runner and preserve exact reconstruction checks. -/
def constructionCases : List (Script × Bool) :=
  [(sql "", true), (sql "CREATE TABLE t(a)", false),
    (sql "SELECT 1 FROM absent", false), (sql "BEGIN", false),
    (sql "SELECT random()", false)]

/-- A real cancellation token interrupts owned reduction and restores speculative state. -/
def canceledAttempt : TermElabM Unit := do
  modifyInfoState fun state => { state with enabled := true }
  let goal ← mkFreshExprMVar (mkConst ``True)
  let messages := (← getThe Core.State).messages.toList.length
  let trees := (← getInfoState).trees.size
  let token ← IO.CancelToken.new
  -- Only this test harness catches the interrupt that the checking API must propagate.
  let _ : MonadExceptOf Exception TermElabM := MonadAlwaysExcept.except
  let interrupted ← try
    discard <| withTheReader Core.Context (fun context => { context with cancelTk? := some token }) <|
      Check.withinBudget 200000 do
        goal.mvarId!.assign (mkConst ``True.intro)
        logError "discard this canceled diagnostic"
        pushInfoTree (.hole goal.mvarId!)
        token.set
        Check.normalizedData (mkApp (mkConst ``Script.statements) (mkConst ``bytesAndReal))
    pure false
  catch error =>
    if error.isInterrupt then pure true else throw error
  unless interrupted && !(← goal.mvarId!.isAssigned) &&
      (← getThe Core.State).messages.toList.length == messages &&
      (← getInfoState).trees.size == trees do
    throwError "cancellation did not propagate with complete speculative cleanup"

/-- Cancel after the first cell in the shared traversal. The next fixed Plausible draw
must observe the token, rather than finishing the complete proposal first. -/
def canceledGeneration : TermElabM Unit := do
  let token ← IO.CancelToken.new
  let drawn ← IO.mkRef (0 : Nat)
  let some base := Sampling.schema [("t", ["a", "b"])] | throwError "invalid fixture schema"
  let cell : StateT StdGen TermElabM Value := do
    let value ← Check.drawValue [] 2
    drawn.modify (· + 1)
    token.set
    return value
  let _ : MonadExceptOf Exception TermElabM := MonadAlwaysExcept.except
  let interrupted ← try
    discard <| withTheReader Core.Context (fun context => { context with cancelTk? := some token }) <|
      Check.withinBudget 200000 do
        discard <| (Sampling.selectCells base.raw.catalog (pure 1) cell).run (mkStdGen 0)
    pure false
  catch error => if error.isInterrupt then pure true else throw error
  unless interrupted && (← drawn.get) == 1 do
    throwError "generation did not stop between its first and second cell draws"

/-- A raw zero-column shape still checks each row, and a large requested range must
not allocate eagerly before the first row check. Valid database generation excludes this
shape; the shared traversal accepts raw catalogs and therefore checks it explicitly. -/
def canceledEmptyRows : TermElabM Unit := do
  let token ← IO.CancelToken.new
  let calls ← IO.mkRef (0 : Nat)
  let catalog : Catalog := [{ name := Model.Identifier.ofString "empty", entry := .table { columns := [] } }]
  let check : TermElabM Unit := do
    checkSystem "fixture row boundary"
    calls.modify (· + 1)
    if (← calls.get) == 2 then token.set
  let _ : MonadExceptOf Exception TermElabM := MonadAlwaysExcept.except
  let interrupted ← try
    discard <| withTheReader Core.Context (fun context => { context with cancelTk? := some token }) <|
      Check.withinBudget 100 do
        Sampling.selectCells catalog (pure 1000000) (pure .null) check
    pure false
  catch error => if error.isInterrupt then pure true else throw error
  unless interrupted && (← calls.get) == 2 do
    throwError "empty-column rows did not check cancellation incrementally"

/-- The checker's finite depth limit restores assignments, diagnostics and the caller's
options after exhaustion. Zero disables work and cannot request unlimited recursion. -/
def depthLimitedAttempt : TermElabM Unit := do
  let goal ← mkFreshExprMVar (mkConst ``True)
  let started ← IO.mkRef false
  let priorDepth := maxRecDepth.get (← getOptions)
  let messages := (← getThe Core.State).messages.toList.length
  let trees := (← getInfoState).trees.size
  let outcome ← Check.check (mkConst ``True) 200000 (recursionLimit := 128)
    (prove := fun _ => do
      started.set true
      goal.mvarId!.assign (mkConst ``True.intro)
      logError "discard this depth-limited attempt"
      pushInfoTree (.hole goal.mvarId!)
      discard <| Check.scriptValue (mkApp (mkConst ``allocationScript) (toExpr (4000000 : Nat)))
      return none)
  let .unknown := outcome.result | throwError "depth exhaustion became a result"
  unless (← started.get) && !(← goal.mvarId!.isAssigned) &&
      maxRecDepth.get (← getOptions) == priorDepth &&
      (← getThe Core.State).messages.toList.length == messages &&
      (← getInfoState).trees.size == trees do
    throwError "depth exhaustion did not restore the caller's state and limit"
  let .unknown := (← Check.check (mkConst ``True) 200000 (recursionLimit := 0)).result
    | throwError "zero requested unlimited recursion"

elab "check_bounded_search_data" : command => Command.liftTermElabM do
  let started ← IO.monoMsNow
  let reason ← IO.mkRef "no exhaustion"
  let result ← Check.withinBudget 2000 <| tryCatchRuntimeEx
    (Check.scriptValue (mkApp (mkConst ``allocationScript) (toExpr (4000000 : Nat))))
    (fun error => do
      reason.set (if error.isMaxHeartbeat then "heartbeats" else if error.isMaxRecDepth then "recursion" else "other")
      throw error)
  unless result.isNone do throwError "expensive data escaped the cooperative checking budget"
  logInfo m!"bounded data exhaustion: {← reason.get}; {(← IO.monoMsNow) - started} ms"
  canceledAttempt
  canceledGeneration
  canceledEmptyRows
  depthLimitedAttempt
  let first ← Check.visitCandidates (mkConst ``True)
    { schema := some (mkConst ``deferredSchema), randomSamples := 1000000000 }
    (fun witness => pure witness.database)
  unless first == some (Lean.mkConst ``Database.empty) do
    throwError "later generation prevented accepting the empty candidate"
  let generated ← Check.randomCandidate Sampling.defaultSchema.raw [] 2 0 2
  let some raw := generated | throwError "the ordinary seeded proposal was rejected"
  discard <| Check.databaseValue (databaseExpr raw)
  unless raw.rows.all (fun rows => rows.length <= 2) do throwError "seeded proposal exceeded its row bound"
  unless raw.rows.map (fun rows => rows.map (·.values)) == [[[.blob []], [.text []]]] do
    throwError "seed zero changed the previously observed count/value draw order"
  for seed in [1, 17] do
    let generated ← Check.randomCandidate Sampling.defaultSchema.raw [] 2 seed 2
    let expected := (Sampling.seeded (Sampling.database Sampling.defaultSchema [] 2) seed 2).toOption.map (·.raw)
    unless generated == expected do throwError "cooperative sampling changed Plausible's seeded proposal"
  let value ← Check.scriptValue (mkConst ``originalDefinition)
  unless value.statements == [(.commit, [])] do
    throwError "compiled override changed the background value"
  unless (← Check.attempt (Check.scriptValue (mkConst ``opaqueScript))).isNone do
    throwError "an opaque computation reached native decoding"
  let value ← Check.scriptValue (mkConst ``bytesAndReal)
  unless value.statements == bytesAndReal.statements do throwError "literal bytes or REAL bits changed"
  for (script, expected) in constructionCases do
    let actual ← Check.dataValue Bool (mkApp2 (mkConst ``Check.constructionMatches)
      (toExpr (script.statements.map (·.1))) (toExpr Database.empty.raw))
    unless actual == expected do throwError "construction validation lost an error or transaction"
  logInfo "bounded data, original definitions, bytes and construction passed"

set_option maxHeartbeats 10000000 in
check_bounded_search_data

end SearchBudgetFixture
