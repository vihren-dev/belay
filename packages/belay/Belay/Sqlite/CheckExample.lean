import Belay.Sqlite.CheckInputs
import Belay.Sqlite.SqlRefute

set_option doc.verso true

/-! Editor examples are parsed and checked as independent proofs of the original statement.
Rendered witness terms remain untrusted until the explicit refutation tactic checks them. -/

namespace Belay.Sqlite.Check
open Lean Meta Elab Term

/-- Print a term with qualified names, then parse it without using expression metadata as
an assertion of correctness. The enclosing example is certified separately. -/
private def printedTerm (expression : Expr) : TermElabM (TSyntax `term) := do
  let text ← withOptions (fun options => pp.deepTerms.set (pp.proofs.set
    (pp.fullNames.set options true) true) true) <| ppExpr expression
  let .ok parsed :=  Parser.runParserCategory (← getEnv) `term text.pretty
    | throwError "SQL example term could not be printed as Lean syntax"
  return ⟨parsed⟩

/-- Produce an explicit refutation tactic with separate execution and quantified inputs.
This syntax does not search: the primitive checks all supplied terms and preconditions. -/
private def witnessTactic (witness : Witness) : TermElabM (TSyntax `tactic) := do
  let database ← printedTerm witness.database
  let environment ← printedTerm witness.environment
  let inputs ← witness.named.mapM fun (name, value) => do
    let value ← printedTerm value
    `(sqlCheckInput| (input $(mkIdent name):ident := $value))
  `(tactic| sql_refute (db := $database) (env := $environment) $inputs:sqlCheckInput*)

/-- Render an independently checked example for a proved or refuted original proposition.
The original declaration and its peers remain excluded. The appended example disables only
its own automatic search, because its explicit proof is already checked. Unknown has no
artifact. Failure to print or recheck an artifact rejects it rather than offering unchecked code. -/
def checkedExample (proposition : Expr) (outcome : Outcome) (excluded : Array Name := #[]) :
    TermElabM String := do
  let (target, tactic) ← match outcome.result with
    | .unknown => throwError "an unknown SQL result has no checked example"
    | .proved proof => pure (proposition, (⟨proof.tactic⟩ : TSyntax `tactic))
    | .refuted witness _ => pure (mkNot proposition, ← witnessTactic witness)
  let type ← printedTerm target
  let command ← `(command| example : $type := by $tactic:tactic)
  let text := (← PrettyPrinter.ppCommand ⟨printableScript command⟩).pretty
  let .ok parsed := Parser.runParserCategory (← getEnv) `command text
    | throwError "SQL example could not be printed as a Lean command"
  let `(command| example : $parsedType := by $parsedTactic:tactic) := parsed
    | throwError "SQL example changed shape while printing"
  withoutErrToSorry do
    let parsedTarget ← elabType parsedType
    synthesizeSyntheticMVarsNoPostponing
    let parsedTarget ← instantiateMVars parsedTarget
    let proof ← proveWith parsedTarget parsedTactic excluded
    discard <| certify target proof.proof excluded
  return "\n\nset_option sql.check false in\n" ++ text ++ "\n"

end Belay.Sqlite.Check
