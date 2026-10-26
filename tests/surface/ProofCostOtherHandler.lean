import Lean

/-! A third-party handler for {lit}`declaration` commands, to test that the collector still lets
other handlers elaborate their commands. It claims every theorem named {lit}`claimed_by_other` and
replaces it with the theorem {lit}`claimed_expanded`, which goes through all handlers again. It
logs and then declines every other command, as a handler of another library might. -/

open Lean Elab Command

namespace ProofCostOtherHandler

/-- Claim one theorem name; decline everything else after a message that Lean must discard. -/
@[command_elab Lean.Parser.Command.declaration]
def claimTheorem : CommandElab := fun stx => do
  unless (stx.find? (·.isIdent)).map (·.getId) == some `claimed_by_other do
    logInfo "OTHER_HANDLER_DECLINED"
    throwUnsupportedSyntax
  logInfo "OTHER_HANDLER_CLAIMED"
  elabCommand (← `(theorem $(mkIdent `claimed_expanded) : (List.range 40).length = 40 := by decide))

end ProofCostOtherHandler
