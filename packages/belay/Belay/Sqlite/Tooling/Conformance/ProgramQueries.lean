import Lean.Elab.Tactic.Basic
import Belay.Sqlite.Programs.Reasoning.Program

set_option doc.verso true

/-! The programs that read the result of one statement (ADR 0017, D1, the row of S3):
{lit}`query s` gives the rows of the statement of script {lit}`s` or its error code, and
{lit}`single s` gives its only value. Each one takes a script of exactly one statement of any
form, so that {lit}`INSERT ... RETURNING` gives its rows; the argument {lit}`one` checks it where
the script is written. {lit}`List.allOk` tells whether outputs have no error. -/

namespace Belay.Sqlite

open Lean Elab Tactic

/-- Two results of {lit}`query`, or of any {lit}`Except`, are equal when both are errors with equal
errors or both are values with equal values. So {lit}`decide` compares the value of a run of
{lit}`query` with an expected value. -/
instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error first, .error second =>
    if same : first = second then isTrue (same ▸ rfl) else isFalse fun equal => same (Except.error.inj equal)
  | .ok first, .ok second =>
    if same : first = second then isTrue (same ▸ rfl) else isFalse fun equal => same (Except.ok.inj equal)
  | .error _, .ok _ => isFalse nofun
  | .ok _, .error _ => isFalse nofun

end Belay.Sqlite
