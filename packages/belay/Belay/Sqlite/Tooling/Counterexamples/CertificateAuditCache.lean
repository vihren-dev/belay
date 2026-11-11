import Lean.Environment
import Lean.CoreM

set_option doc.verso true

/-! The constants that the certificate audit has accepted during one checking operation. A
check certifies many candidates of one claim, and each certificate depends on mostly the same
constants. The audit walks the closure of each constant once for the operation and not once
for each certificate. -/

namespace Belay.Sqlite.Check

open Lean

/-- The accepted constants of one checking operation. The audit uses the record only when its
own exclusions are the same, because a constant is accepted only relative to them. Only
constants of the starting environment are recorded: a speculative attempt can add a constant,
discard it, and a later attempt can add another constant with the same name. -/
structure AuditCache where
  /-- The excluded declarations of the operation. -/
  excluded : Array Name
  /-- The environment at the start of the operation. -/
  environment : Environment
  /-- The constants whose complete closure the audit has accepted. It is a reference, so that an
  accepted constant stays accepted when a failed attempt restores the elaboration state. -/
  accepted : IO.Ref NameSet

instance : Nonempty AuditCache :=
  ⟨{ excluded := #[], environment := Classical.ofNonempty, accepted := Classical.ofNonempty }⟩

/-- The record of the current checking operation, when there is one. The state is local to
the environment branch, so parallel elaboration of other declarations does not see it. -/
initialize auditCacheExtension : EnvExtension (Option AuditCache) ←
  registerEnvExtension (pure none) (asyncMode := .local)

/-- Run an operation with a new record of accepted constants for the exclusions
{name}`AuditCache.excluded`, and restore the previous record afterwards. Use it around one
checking operation; nested operations each get their own record. -/
def withAuditCache [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] [MonadFinally m]
    (excluded : Array Name) (action : m α) : m α := do
  let previous := auditCacheExtension.getState (← getEnv)
  let accepted ← (IO.mkRef {} : BaseIO (IO.Ref NameSet))
  let cache : AuditCache := { excluded, environment := ← getEnv, accepted }
  modifyEnv (auditCacheExtension.setState · (some cache))
  try action
  finally modifyEnv (auditCacheExtension.setState · previous)

/-- The record that applies to an audit with these exclusions, if any. -/
def currentAuditCache (environment : Environment) (excluded : Array Name) : Option AuditCache :=
  (auditCacheExtension.getState environment).filter (·.excluded == excluded)

end Belay.Sqlite.Check
