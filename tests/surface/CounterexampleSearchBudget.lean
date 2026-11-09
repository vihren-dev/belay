import Belay
import Belay.Sqlite.CheckData
import Belay.Sqlite.CheckReplayData

open Lean Elab Term Meta Belay.Sqlite

/-! The checker computes background data with compiled code in a dedicated task
(`Check.compiledValue`), and the kernel checks each value. This fixture checks that a compiled
override or an opaque constant is not run, that cancellation and the time limit stop the wait,
and that the check restores the caller's state, without timing assertions. -/

namespace SearchBudgetFixture

/-- The sum of the numbers below {lean}`count`: costly in time, but constant in stack and memory.
The time limit and the cancellation stop only the wait, so the computation runs on until Lean
exits. A non-tail-recursive fold, such as {name}`List.sum` over {lean}`List.range count`, then
overflows the stack (seen on macOS CI); this loop cannot. -/
def costlySum (count : Nat) : Nat := go count 0 where
  /-- Adds the numbers below the first argument to the total. -/
  go : Nat → Nat → Nat
    | 0, total => total
    | rest + 1, total => go rest (total + rest)

/-- This is a finite but deliberately costly computation in a raw script-data projection. -/
def costlyScript (count : Nat) : Script :=
  ⟨[(.commit, [.integer (Int.ofNat (costlySum count))])]⟩

/-- The compiled implementation deliberately returns different statement data. -/
def differentImplementation : Script := ⟨[(.rollback, [])]⟩

/-- A definition's logical meaning remains authoritative even with a different implementation. -/
@[implemented_by differentImplementation]
def originalDefinition : Script := ⟨[(.commit, [])]⟩

/-- The checker does not run compiled code of an opaque constant, whose definition the kernel
cannot see. -/
opaque opaqueScript : Script := ⟨[(.commit, [])]⟩

/-- A schema without a definition must not delay an accepted earlier candidate. -/
opaque deferredSchema : Database := Database.empty

/-- SQL values include UInt8/UInt64 constructor data, not only natural-number literals. -/
def bytesAndReal : Script :=
  ⟨[(.commit, [.blob [0, 255], .text [97, 0, 39], .real 0x3ff8000000000000])]⟩

/-- These operations use the existing model runner and preserve exact reconstruction checks. -/
def constructionCases : List (Script × Bool) :=
  [(sql "", true), (sql "CREATE TABLE t(a)", false),
    (sql "SELECT 1 FROM absent", false), (sql "BEGIN", false),
    (sql "SELECT random()", false)]

/-- A real cancellation token interrupts the wait for compiled data and restores speculative state. -/
def canceledAttempt : TermElabM Unit := do
  modifyInfoState fun state => { state with enabled := true }
  let goal ← mkFreshExprMVar (mkConst ``True)
  let messages := (← getThe Core.State).messages.toList.length
  let trees := (← getInfoState).trees.size
  let token ← IO.CancelToken.new
  -- Whether the wait returned; the interrupt must come before it returns.
  let returned ← IO.mkRef false
  -- Only this test harness catches the interrupt that the checking API must propagate.
  let _ : MonadExceptOf Exception TermElabM := MonadAlwaysExcept.except
  let interrupted ← try
    discard <| withTheReader Core.Context (fun context => { context with cancelTk? := some token }) <|
      Check.withinBudget 200000 do
        goal.mvarId!.assign (mkConst ``True.intro)
        logError "discard this canceled diagnostic"
        pushInfoTree (.hole goal.mvarId!)
        token.set
        -- The token is set before the wait starts, and awaitCompiled checks it only in its wait
        -- loop, after it starts the task: the interrupt comes from the wait. The count is a
        -- runtime value, so that the sum is computed in the task.
        let count ← (pure 100000000 : IO Nat)
        discard <| Check.awaitCompiled fun _ => costlySum count
        returned.set true
    pure false
  catch error =>
    if error.isInterrupt then pure true else throw error
  unless interrupted && !(← returned.get) && !(← goal.mvarId!.isAssigned) &&
      (← getThe Core.State).messages.toList.length == messages &&
      (← getInfoState).trees.size == trees do
    throwError "cancellation did not propagate with complete speculative cleanup"

/-- {name}`Sampling.candidates` keeps the order of the search: the targeted databases, table contents with fewest rows first, then the seeded random databases. The limit
cuts the list. -/
def candidateOrder : TermElabM Unit := do
  let base := Sampling.defaultSchema
  let all := Sampling.candidates base [] none 2 3 0 2 100000
  let targeted := (Sampling.targeted base []).filter (·.raw.rows.all (·.length ≤ 2))
  let seeded := (List.range 3).filterMap fun seed =>
    (Sampling.seeded (Sampling.touchedDatabase base [] 2 none (.integer 0)) seed 2).toOption
  let raws := all.toList.map (·.raw)
  unless raws.take targeted.length == targeted.map (·.raw) do
    throwError "the search does not start with the targeted databases"
  unless raws.drop (raws.length - seeded.length) == seeded.map (·.raw) do
    throwError "the seeded random databases are not the last candidates"
  let contents := (raws.drop targeted.length).take (raws.length - targeted.length - seeded.length)
  let totals := contents.map fun raw => (raw.rows.map List.length).sum
  unless !contents.isEmpty && (totals.zip (totals.drop 1)).all fun (a, b) => a ≤ b do
    throwError "table contents are not in order of their row count"
  for limit in [0, 1, targeted.length, targeted.length + 1, all.size + 1] do
    unless (Sampling.candidates base [] none 2 3 0 2 limit).size == min limit all.size do
      throwError "the limit {limit} does not cut the candidates"

/-- Recursion of the elaborator to the given depth. -/
def deeper : Nat → TermElabM Unit
  | 0 => pure ()
  | depth + 1 => withIncRecDepth (deeper depth)

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
      deeper 1000
      return none)
  let .unknown := outcome.result | throwError "depth exhaustion became a result"
  unless (← started.get) && !(← goal.mvarId!.isAssigned) &&
      maxRecDepth.get (← getOptions) == priorDepth &&
      (← getThe Core.State).messages.toList.length == messages &&
      (← getInfoState).trees.size == trees do
    throwError "depth exhaustion did not restore the caller's state and limit"
  let .unknown := (← Check.check (mkConst ``True) 200000 (recursionLimit := 0)).result
    | throwError "zero requested unlimited recursion"

/-- Checks that a generated candidate carries its value ({name}`Check.Witness.value`) and that the
witness text uses a carried value without evaluating the term: here the term is the opaque
{name}`deferredSchema`, which the checker does not evaluate. -/
def carriedValues : TermElabM Unit := do
  let generated ← Check.visitCandidates (mkConst ``True) { screen := some fun _ _ => true }
    fun witness _ => if witness.value.isSome then pure witness else throwError "not generated"
  let some { database, value := some value, .. } := generated | throwError "no generated candidate"
  unless database == Check.generatedExpr value.raw none do
    throwError "the carried value is not the value of the generated term"
  let some _ ← Check.attempt
      (Check.witnessText { database := mkConst ``deferredSchema, value := some Database.empty })
    | throwError "the witness text evaluated the term instead of using the carried value"

elab "check_bounded_search_data" : command => Command.liftTermElabM do
  let started ← IO.monoMsNow
  let stopped ← Check.withCompiledLimit 20 do
    let result ← Check.attempt
      (Check.scriptValue (mkApp (mkConst ``costlyScript) (toExpr (100000000 : Nat))))
    pure (result.isNone && (← Check.compiledLimitExpired))
  unless stopped do throwError "expensive data escaped the time limit of compiled work"
  -- Only the waits for compiled work count: time in the elaborator does not use up the limit.
  let left ← Check.withCompiledLimit 50 do
    IO.sleep 200
    Check.compiledTimeLeft
  unless left == some 50 do throwError "time outside compiled work used up the time limit: {left}"
  logInfo m!"bounded data: time limit; {(← IO.monoMsNow) - started} ms"
  canceledAttempt
  candidateOrder
  carriedValues
  depthLimitedAttempt
  -- A schema without a definition must not delay the empty candidate.
  let first ← Check.visitCandidates (mkConst ``True)
    { schema := some (mkConst ``deferredSchema), randomSamples := 1000000000, screen := some fun _ _ => true }
    (fun witness _ => pure witness.database)
  unless first == some (Lean.mkConst ``Database.empty) do
    throwError "later generation prevented accepting the empty candidate"
  unless (← Check.attempt (Check.scriptValue (mkConst ``originalDefinition))).isNone do
    throwError "the checker ran a compiled override"
  unless (← Check.attempt (Check.scriptValue (mkConst ``opaqueScript))).isNone do
    throwError "the checker ran compiled code of an opaque constant"
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
