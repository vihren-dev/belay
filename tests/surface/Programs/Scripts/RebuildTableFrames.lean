import RebuildKeepsInvariant

/-! Test `ResolveState.tablePosition`, which applies `Resolved.Statement.keeps` at each step.
Dropping customers moves sessions from position 1 to position 0. With enforcement on the drop
can delete sessions by cascade, so the result is none. Updating sessions can change its rows,
and renaming customers rewrites its foreign key, so both scripts also give none. -/
open Belay.Sqlite Belay.Sqlite.Model RebuildGuide
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Resolve the test script and apply the whole-script table check at the starting position.
Resolution failure is separate from a frame refusal. -/
private def frame (script : Script) (start : Nat) : Except Restriction (Option Nat) := do
  let initial := sample.raw.connection.resolveState
  let (resolved, _) ← resolveFrom runContext 0 initial (script.statements.map Prod.fst)
  return initial.tablePosition resolved script.statements.length start

example : frame makeStrict 1 = .ok (some 0) := by decide +kernel
example : frame makeStrictWrongEnforced 1 = .ok none := by decide +kernel
example : frame (sql "UPDATE sessions SET expires_at = 1") 1 = .ok none := by decide +kernel
example : frame (sql "ALTER TABLE customers RENAME TO clients") 1 = .ok none := by decide +kernel
