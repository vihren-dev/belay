import Belay
import Belay.Sqlite.CheckBudget
import Belay.Sqlite.CheckCandidates

open Belay.Sqlite Lean Elab Term Meta

/-! The shared checker must certify either sign of the original claim and roll back
speculative elaboration work. Its internal reifiers must preserve ordinary imported display.
No finite candidate sequence proves a universal fact. -/

/-- info: [Except.ok (Belay.Sqlite.Model.Value.integer 7)] -/
#guard_msgs in
#eval ([Except.ok (.integer 7)] : List (Except String Value))

-- Except reification must also remain unavailable for types unrelated to SQL output.
run_meta do
  let type := mkApp2 (mkConst ``Except [.zero, .zero]) (mkConst ``String) (mkConst ``Nat)
  if (← synthInstance? (mkApp (mkConst ``ToExpr [.zero]) type)).isSome then
    throwError "the SQL checker exported a general Except reifier"

namespace SearchCoreFixture

/-- Every database having a row in a nonexistent table is false. -/
def missing : Prop := ∀ db : Database, Holds (sql "SELECT 1 FROM absent") db

/-- A premise that the empty candidate cannot satisfy prevents its use as a witness. -/
def guarded : Prop := ∀ db : Database, False → Empty (sql "SELECT 1") db

/-- Disabling proof automation isolates candidate search in the negative tests. -/
def noProof (_ : Expr) : TermElabM (Option Check.Proven) := pure none

/-- An ordinary failure after assigning a goal and logging output must leave no changes. -/
def failedAttempt : TermElabM Unit := do
  modifyInfoState fun state => { state with enabled := true }
  let goal ← mkFreshExprMVar (mkConst ``True)
  let beforeMessages := (← getThe Core.State).messages.toList.length
  let beforeInfo := (← getInfoState).trees.size
  let result ← Check.attempt do
    goal.mvarId!.assign (mkConst ``True.intro)
    logError "discard this speculative diagnostic"
    pushInfoTree (.hole goal.mvarId!)
    throwError "discard this failed attempt"
    pure ()
  unless result.isNone && !(← goal.mvarId!.isAssigned) do
    throwError "a failed SQL attempt retained a metavariable assignment"
  unless (← getThe Core.State).messages.toList.length == beforeMessages &&
      (← getInfoState).trees.size == beforeInfo do
    throwError "a failed SQL attempt retained diagnostics or editor information"

/-- A custom tactic can fail after solving its goal and emitting speculative diagnostics. -/
elab "assign_then_fail" : tactic => do
  (← Lean.Elab.Tactic.getMainGoal).assign (mkConst ``True.intro)
  logError "discard this custom tactic diagnostic"
  throwError "custom tactic failed after assignment"

/-- A term-producing tactic can emit an error without throwing; its script is unusable. -/
elab "assign_with_error" : tactic => do
  (← Lean.Elab.Tactic.getMainGoal).assign (mkConst ``True.intro)
  Lean.Elab.Tactic.replaceMainGoal []
  logError "discard this proof script error"

/-- A failed custom tactic leaves no diagnostic and does not prevent the next proof attempt. -/
def failedTactic : TermElabM Unit := do
  let beforeMessages := (← getThe Core.State).messages.toList.length
  let beforeInfo := (← getInfoState).trees.size
  let result ← Check.attempt (Check.proveWith (mkConst ``True) (← `(tactic| assign_then_fail)))
  unless result.isNone && (← getThe Core.State).messages.toList.length == beforeMessages &&
      (← getInfoState).trees.size == beforeInfo do
    throwError "failed custom automation retained speculative state"
  unless (← Check.attempt (Check.proveWith (mkConst ``True) (← `(tactic| assign_with_error)))).isNone do
    throwError "a script that emits an error became a successful proof suggestion"

/-- A heartbeat stop restores assignments and messages, then reports no result. -/
def exhaustedAttempt : TermElabM Unit := do
  modifyInfoState fun state => { state with enabled := true }
  let goal ← mkFreshExprMVar (mkConst ``True)
  let beforeMessages := (← getThe Core.State).messages.toList.length
  let beforeInfo := (← getInfoState).trees.size
  let result ← Check.withinBudget 1 do
    goal.mvarId!.assign (mkConst ``True.intro)
    logError "discard this exhausted diagnostic"
    pushInfoTree (.hole goal.mvarId!)
    IO.addHeartbeats 100000
    pure ()
  unless result.isNone && !(← goal.mvarId!.isAssigned) do
    throwError "an exhausted SQL attempt retained a result or assignment"
  unless (← getThe Core.State).messages.toList.length == beforeMessages &&
      (← getInfoState).trees.size == beforeInfo do
    throwError "an exhausted SQL attempt retained diagnostics or editor information"

elab "check_search_core" : command => Command.liftTermElabM do
  failedAttempt
  failedTactic
  exhaustedAttempt
  let witness : Check.Witness := { database := mkConst ``Database.empty }
  let .proved proven ← Check.checkCandidates (mkConst ``True) (pure #[witness])
    | throwError "proof search did not recover after rejected attempts"
  discard <| Check.proveWith (mkConst ``True) proven.tactic
  let .refuted _ proof ← Check.checkCandidates (mkConst ``missing) (pure #[witness]) noProof
    | throwError "the shared candidate search missed the explicit checked witness"
  discard <| Check.certify (mkNot (mkConst ``missing)) proof
  let .unknown ← Check.checkCandidates (mkConst ``guarded) (pure #[witness]) noProof
    | throwError "a false implication premise became a counterexample"
  let wrong := fun _ => pure (some ({ proof := mkConst ``True.intro, tactic := Syntax.missing } : Check.Proven))
  let .unknown ← Check.checkCandidates (mkConst ``False) (pure #[]) wrong
    | throwError "the search trusted a candidate proof of a different proposition"
  let unrelated := fun _ => do
    let tactic ← `(tactic| fail "this script does not prove True")
    pure (some ({ proof := mkConst ``True.intro, tactic } : Check.Proven))
  let .unknown ← Check.checkCandidates (mkConst ``True) (pure #[]) unrelated
    | throwError "a certified term concealed an unrelated proposed proof script"
  let .none ← Check.withinBudget (α := Unit) 0 (throwError "a disabled check executed")
    | throwError "zero budget did not disable checking"
  logInfo "shared checker certificates and rollback passed"

check_search_core

end SearchCoreFixture
