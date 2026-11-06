import Lean.Meta.Eval
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Elab.Term

set_option doc.verso true

/-! Compiled work of a SQL check. The checker computes candidates, screens and data with the
compiled code of their definitions, which is fast and counts no heartbeats. The kernel still
decides every result. This module bounds compiled work by a time limit for the whole check, and
refuses to compile terms that reach code whose implementation is not its definition. -/

namespace Belay.Sqlite.Check

open Lean Meta Elab Term

/-- The time limit of the compiled work of one checking operation. Only the time that the
operation waits for compiled work counts; the elaborator and the kernel count heartbeats
instead. -/
structure CompiledLimit where
  /-- The milliseconds of waiting for compiled work that the operation has left. It is a
  reference, so that the time stays spent when a failed attempt restores the elaboration state. -/
  remaining : IO.Ref Nat
  /-- Whether compiled work of the operation reached the limit. It is a reference for the same
  reason. -/
  expired : IO.Ref Bool
  /-- Why the search of the operation ended without a result, when a limit or a missing screen
  explains it. It is a reference for the same reason. -/
  reason : IO.Ref (Option String)

instance : Nonempty CompiledLimit :=
  ⟨{ remaining := Classical.ofNonempty, expired := Classical.ofNonempty, reason := Classical.ofNonempty }⟩

/-- The time limit of the current checking operation, when there is one. The state is local to
the environment branch, as the record of the certificate audit is. -/
initialize compiledLimitExtension : EnvExtension (Option CompiledLimit) ←
  registerEnvExtension (pure none) (asyncMode := .local)

/-- Run an operation that may wait for compiled work for the given number of milliseconds in
total, and restore the previous limit afterwards. Use it around one checking operation. -/
def withCompiledLimit [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] [MonadFinally m]
    (milliseconds : Nat) (action : m α) : m α := do
  let previous := compiledLimitExtension.getState (← getEnv)
  let expired ← (IO.mkRef false : BaseIO (IO.Ref Bool))
  let reason ← (IO.mkRef none : BaseIO (IO.Ref (Option String)))
  let remaining ← (IO.mkRef milliseconds : BaseIO (IO.Ref Nat))
  modifyEnv (compiledLimitExtension.setState · (some { remaining, expired, reason }))
  try action
  finally modifyEnv (compiledLimitExtension.setState · previous)

/-- Whether the compiled work of the current operation reached its time limit. False outside a
checking operation. -/
def compiledLimitExpired : CoreM Bool := do
  match compiledLimitExtension.getState (← getEnv) with
  | some limit => limit.expired.get
  | none => return false

/-- The text of an unknown result that the time limit stopped. -/
def timeLimitReason : String :=
  "the search reached its time limit; increase sql.checkTimeLimit to search longer"

/-- Record why the search of the current operation ends without a result. The first reason
stays. Outside a checking operation it does nothing. -/
def recordReason (text : String) : CoreM Unit := do
  if let some limit := compiledLimitExtension.getState (← getEnv) then
    limit.reason.modify (·.or (some text))

/-- The recorded reason of the current operation ({name}`recordReason`), if any. -/
def recordedReason : CoreM (Option String) := do
  match compiledLimitExtension.getState (← getEnv) with
  | some limit => limit.reason.get
  | none => return none

/-- Wait for compiled work in a dedicated task. The wait checks cancellation. Its time counts
against the time limit of the operation ({name}`withCompiledLimit`); when the time that is left
runs out, the wait records the limit and throws.
Compiled code cannot be stopped, so an abandoned task runs to the end of its computation; its
result is not used. Outside a checking operation there is no time limit. -/
def awaitCompiled (work : Unit → α) : CoreM α := do
  let limit := compiledLimitExtension.getState (← getEnv)
  if let some limit := limit then
    if ← limit.expired.get then throwError timeLimitReason
  let start ← IO.monoMsNow
  let deadline ← match limit with
    | some limit => pure (some (start + (← limit.remaining.get)))
    | none => pure none
  let task := Task.spawn (prio := .dedicated) work
  repeat
    if ← IO.hasFinished task then
      if let some limit := limit then
        let waited := (← IO.monoMsNow) - start
        limit.remaining.modify (· - waited)
      return task.get
    Core.checkInterrupted
    if let (some limit, some deadline) := (limit, deadline) then
      if (← IO.monoMsNow) ≥ deadline then
        limit.remaining.set 0
        limit.expired.set true
        limit.reason.modify (·.or (some timeLimitReason))
        throwError timeLimitReason
    IO.sleep 1
  return task.get

/-- The roots of the modules whose compiled code the checker runs without looking into it: Lean's
own modules and the modules of this repository's packages. -/
def trustedModuleRoots : Array Name := #[`Init, `Std, `Lean, `Belay]

/-- Why compiled code of the constant can differ from its definition: an {lit}`implemented_by` or
{lit}`extern` implementation, an {lit}`unsafe` constant, or an opaque constant, which is how Lean
keeps a {lit}`partial` definition. None for other constants. -/
def compiledDifference? (environment : Environment) (name : Name) : Option String := do
  let info ← environment.find? name
  if (Compiler.getImplementedBy? environment name).isSome then some "has an implemented_by implementation"
  else if isExtern environment name then some "has an extern implementation"
  else if info.isUnsafe then some "is unsafe"
  else if info matches .opaqueInfo _ then some "is opaque or partial"
  else none

/-- Check that compiled code of the term computes what its definitions say: no constant that the
term reaches, outside the modules of {name}`trustedModuleRoots`, has a compiled implementation
that can differ from its definition ({name}`compiledDifference?`). The walk follows the values of
definitions outside those modules. It throws with the first such constant. -/
def checkCompiledClosure (expression : Expr) : MetaM Unit := do
  let environment ← getEnv
  let trusted (name : Name) : Bool :=
    match environment.getModuleIdxFor? name with
    | some index => trustedModuleRoots.contains (environment.header.moduleNames[index.toNat]!).getRoot
    | none => false
  let mut pending := expression.getUsedConstants
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    checkSystem "SQL compiled closure"
    let name := pending.back!
    pending := pending.pop
    if seen.contains name || trusted name then continue
    seen := seen.insert name
    if let some reason := compiledDifference? environment name then
      throwError "SQL checking does not run compiled code of {.ofConstName name}, which {reason}"
    -- Compiled code erases proofs, so the walk follows definitions and not theorems.
    if let some (.defnInfo definition) := environment.find? name then
      pending := pending ++ definition.value.getUsedConstants

/-- Compile a closed term of the given type. Only {lit}`compiledValue` and the screen use it. -/
private unsafe def compileUnsafe (α : Type) [Nonempty α] (type expression : Expr) : TermElabM α :=
  evalExpr α type expression

/-- Compile a closed term of the given type with Lean's compiler ({name}`Lean.Meta.evalExpr`). -/
@[implemented_by compileUnsafe]
opaque compileTerm (α : Type) [Nonempty α] (type expression : Expr) : TermElabM α

/-- Compile a closed term after its closure check ({name}`checkCompiledClosure`), and compute its
value in a dedicated task ({name}`awaitCompiled`). The result is untrusted until the caller checks
it against the term in the kernel. -/
def compiledValue (α : Type) [Nonempty α] (type expression : Expr) : TermElabM α := do
  checkCompiledClosure expression
  let unit := Lean.mkConst ``Unit
  let thunk ← compileTerm (Unit → α) (← mkArrow unit type) (.lam `unit unit expression .default)
  awaitCompiled thunk

end Belay.Sqlite.Check
