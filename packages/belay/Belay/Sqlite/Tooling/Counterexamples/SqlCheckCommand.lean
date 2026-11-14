import Belay.Sqlite.Tooling.Counterexamples.CheckInputs
import Belay.Sqlite.Tooling.Counterexamples.CheckDisplay

set_option doc.verso true

/-! The explicit SQL checking command elaborates a proposition in its native local context
and delegates search, certification and replay to the shared checking operation. -/

namespace Belay.Sqlite
open Lean Elab Command Meta

/-- Check a proposition with kernel-certified proof search or a replayable counterexample.
For example, {lit}`#sql_check ∀ db : Database, Empty (sql "SELECT 1") db` reports false.
Optional {lit}`with (schema := database)`, repeated {lit}`(db := database)`,
{lit}`(env := environment)` and {lit}`(input name := value)` guide the same checker.
The inputs direct the search only and do not change the claim.
The {lit}`sql.checkBudget` and {lit}`sql.checkCandidates` options bound the search;
an unknown result proves nothing. The command adds no theorem. -/
syntax (name := sqlCheckCommand) "#sql_check " term
  (" with " sqlCheckInput+)? : command

/-- The note of an unknown answer to a claim that has a search schema from
{lit}`with (schema := shop)` and no {name}`Database.HasCatalog` premise. The input only tells the
search where to look, so the claim can be false on a database of another schema, and no proof of
it exists. Such an answer can hide a claim that is false as written (issue #375). The note tells
the user how to state the claim for the databases of the schema. Other answers get no note. -/
def schemaOnlyDirectsNote (proposition : Expr) (inputs : Array (TSyntax `sqlCheckInput))
    (outcome : Check.Outcome) : MetaM (Option MessageData) := do
  unless outcome.result matches .unknown do return none
  let schemas := inputs.filterMap fun input => match input with
    | `(sqlCheckInput| ($kind:ident := $value)) => if kind.getId == `schema then some value else none
    | _ => none
  let some schema := schemas[0]? | return none
  let premises ← try Check.domainSchemas proposition catch _ => pure #[]
  unless premises.isEmpty do return none
  return some m!"Note: (schema := {schema}) only directs the search. The claim is about all \
    databases, also those of other schemas. To make the claim about the databases of {schema} only, \
    write `on {schema}` after `preserves` or `succeeds`, or add the premise (·.HasCatalog {schema})."

/-- Elaborate the original proposition in the command's local context and display only the
shared checker's result, with the note of {name}`schemaOnlyDirectsNote` when it applies. Normal
Lean cancellation remains attached to this command. -/
@[command_elab sqlCheckCommand]
def elabSqlCheckCommand : CommandElab := fun stx => do
  let `(command| #sql_check $proposition $[with $inputs:sqlCheckInput*]?) := stx
    | throwUnsupportedSyntax
  let message ← runTermElabM fun _ => Term.withoutErrToSorry do
    let proposition ← Term.elabTerm proposition (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    let proposition ← instantiateMVars proposition
    let inputs := inputs.getD #[]
    let outcome ← Check.configuredCheck proposition inputs
    let message ← Check.describe outcome
    return match ← schemaOnlyDirectsNote proposition inputs outcome with
      | some note => message ++ m!"\n{note}"
      | none => message
  logInfo message

end Belay.Sqlite
