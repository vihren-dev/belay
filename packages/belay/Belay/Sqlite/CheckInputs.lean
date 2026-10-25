import Belay.Sqlite.CheckOptions
import Lean.Util.Heartbeats

set_option doc.verso true

/-! Supplied search inputs are ordinary Lean terms. They become proposals for the existing
checker, which still certifies the original proposition and validates each replay. -/

namespace Belay.Sqlite.Check
open Lean Meta Elab Term

/-- One explicit search input. A schema guides generation; repeated databases give an ordered
candidate sequence. Named inputs match quantified binders, including binders named env or schema. -/
declare_syntax_cat sqlCheckInput
syntax "(" ident ":=" term ")" : sqlCheckInput
syntax "(" ident ident ":=" term ")" : sqlCheckInput

/-- Elaborate a supplied term at its source location without error-to-sorry recovery. -/
private def inputTerm (stx : Syntax) (expected : Option Expr := none) : TermElabM Expr :=
  withRef stx <| withoutErrToSorry do
    let value ← elabTerm stx expected
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars value

/-- Add typed explicit inputs to the configured sampler. Every supplied database uses the
same final environment and named inputs, independently of input order. -/
def elaborateInputs (inputs : Array (TSyntax `sqlCheckInput)) : TermElabM SampleConfig := do
  let mut samples := configuredSamples (← getOptions)
  let mut databases := #[]
  let mut environmentSeen := false
  for entry in inputs do
    match entry with
    | `(sqlCheckInput| ($kind:ident := $value)) =>
      if kind.getId == `schema then
        if samples.schema.isSome then throwErrorAt entry "supply only one SQL search schema"
        samples := { samples with schema := some (← inputTerm value (some (mkConst ``Database))) }
      else if kind.getId == `db then
        databases := databases.push (← inputTerm value (some (mkConst ``Database)))
      else if kind.getId == `env then
        if environmentSeen then throwErrorAt entry "supply only one SQL search environment"
        environmentSeen := true
        samples := { samples with environment := ← inputTerm value (some (mkConst ``Env)) }
      else throwErrorAt kind "expected schema, db or env; use (input name := value) for a quantified input"
    | `(sqlCheckInput| ($kind:ident $name:ident := $value)) =>
      unless kind.getId == `input do throwErrorAt kind "expected (input name := value)"
      if samples.named.any (fun entry => entry.1 == name.getId) then
        throwErrorAt name "supply only one value for this quantified input"
      samples := { samples with named := samples.named.push (name.getId, ← inputTerm value) }
    | _ => throwUnsupportedSyntax
  return { samples with witnesses := databases.map fun database =>
    { database, environment := samples.environment, named := samples.named } }

/-- Run the common checker with frontend options and optional supplied terms. Input elaboration
and checking share one heartbeat budget. Type errors retain their input locations; exhaustion
is unknown and cancellation propagates. A displayed proof script is printed, parsed and
checked again against the original proposition inside that budget. Custom generators can use {name}`check` and
{name}`SampleConfig.witnesses` directly, without a notation-specific interface. -/
def configuredCheck (proposition : Expr) (inputs : Array (TSyntax `sqlCheckInput) := #[]) :
    TermElabM Outcome := do
  let options ← getOptions
  let recursionLimit := sql.checkRecursionLimit.get options
  if recursionLimit == 0 then return {}
  let result ← withOptions (maxRecDepth.set · recursionLimit) <|
    withinBudget (sql.checkBudget.get options) do
      let samples ← elaborateInputs inputs
      let remaining := (← getRemainingHeartbeats) / 1000
      let outcome ← check proposition remaining samples (sql.checkShrinkAttempts.get options)
        (recursionLimit := recursionLimit)
      match outcome.result with
      | .proved proof =>
        let printed ← attempt do
          let printable := proof.tactic.rewriteBottomUp fun node =>
            if node.isIdent then mkIdentFrom node node.getId.eraseMacroScopes else node
          let text ← PrettyPrinter.ppTactic ⟨printable⟩
          let .ok tactic := Parser.runParserCategory (← getEnv) `tactic text.pretty
            | throwError "SQL proof script could not be printed as Lean syntax"
          proveWith proposition tactic
        return printed.map (fun proof => { outcome with result := .proved proof }) |>.getD {}
      | .refuted .. | .unknown => return outcome
  return result.getD {}

end Belay.Sqlite.Check
