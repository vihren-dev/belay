import Belay.Sqlite.ClaimExplanation
import Lean.Elab.Command

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Command Term

/-- Explain an elaborated migration preservation, translation or commutation
proposition, a fresh-run claim, an ordinary Std.Do triple or a success claim. For
example, {lit}`#explain M preserves Q where G` describes the original migration-success
domain and the default SQL guard, and {lit}`#explain P ensures andOk ⌜True⌝ where G`
describes the fresh entry and the error policy. It proves no claim. -/
syntax (name := explainMigration) "#explain " term : command

/-- Elaborate a proposition before explaining its supported primitive head
({name}`claimExplanation`). This checks query admission and guard types. Unsupported
propositions receive a source diagnostic rather than an explanation that assigns them
invented semantics. -/
@[command_elab explainMigration]
def elabExplainMigration : CommandElab := fun command => do
  match command with
  | `(#explain $claim) => withRef claim do
    liftTermElabM <| withoutErrToSorry do
      let expression ← elabTermEnsuringType claim (some (mkSort Level.zero))
      synthesizeSyntheticMVarsNoPostponing
      let expression ← instantiateMVars expression
      match claimExplanation expression with
      | some explanation =>
        let written := claim.raw.reprint.getD "<generated migration claim>"
        logInfo m!"Claim: {written}\n{explanation}"
      | none => throwError "Cannot explain this proposition. Use a migration preserves, translates, or commutes with pattern (or its Migration.QueryPreserves, QueryTranslates, Commutes, or CommutesAs primitive), a fresh-run claim (ensures, FreshEnsures or FreshTriple), a Std.Do triple about a Sql program with its standard transformer, or Succeeds."
  | _ => throwUnsupportedSyntax

end Belay.Sqlite
