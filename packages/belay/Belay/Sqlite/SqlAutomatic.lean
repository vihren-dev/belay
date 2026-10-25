import Belay.Sqlite.CheckDeclarations
import Belay.Sqlite.CheckExample
import Belay.Sqlite.CheckDisplay
import Lean.Meta.Tactic.TryThis

set_option doc.verso true

/-! Native command linters check completed SQL statements without replacing declaration
elaboration. Search uses the native cancellation token and no proof-body local assumptions. -/

/-- Check SQL theorem statements automatically. Set false to keep only explicit commands
and tactics. Resource exhaustion remains unknown and never alleges a false statement. -/
register_option sql.check : Bool := {
  defValue := true
  descr := "automatically check SQL theorem statements with the configured finite budget" }

namespace Belay.Sqlite.Check
open Lean Meta Elab Term Command

/-- A checked result and independently checked text to append after the original command. -/
private structure AutomaticResult where
  /-- Only the shared operation supplies truth results and validated SQL replay. -/
  outcome : Outcome
  /-- Independently parsed, elaborated and certified example text. -/
  exampleText : String

/-- Check one original closed statement in its saved environment, retaining the native
cancellation token and the remaining command budget. -/
private def checkStatement (statement : Statement) (excluded : Array Name) :
    TermElabM (Option AutomaticResult) :=
  withEnv statement.context.env <| withOptions (fun _ =>
    maxRecDepth.set statement.context.options (sql.checkRecursionLimit.get statement.context.options)) do
    let options ← getOptions
    if !sql.check.get options || sql.checkRecursionLimit.get options == 0 then return none
    attempt do
      unless (← sqlMention? statement.proposition) == some true do
        throwError "the statement has no available SQL check"
      let remaining := (← getRemainingHeartbeats) / 1000
      let outcome ← check statement.proposition remaining (configuredSamples options)
        (sql.checkShrinkAttempts.get options) (excluded := excluded)
        (recursionLimit := sql.checkRecursionLimit.get options)
      let exampleText ← checkedExample statement.proposition outcome excluded
      return { outcome, exampleText }

/-- Emit only checked results, using a zero-width native suggestion after the command.
The original false statement keeps its error until edited; the added example is independent.
An unknown result has no certificate, so it reports nothing. -/
private def reportStatement (command : Syntax) (statement : Statement)
    (result : AutomaticResult) : TermElabM Unit :=
  withEnv statement.context.env do
    let title ← match result.outcome.result with
      | .refuted .. =>
        logErrorAt statement.ref (← describe result.outcome)
        pure "Add as a regression example"
      | .proved .. => pure "Add checked proof example"
      | .unknown => return
    let position := command.getTailPos?.getD 0
    Meta.Tactic.TryThis.addSuggestion statement.ref
      { suggestion := result.exampleText, toCodeActionTitle? := some (fun _ => title) }
      (origSpan? := some (Syntax.ofRange { start := position, stop := position }))
      (header := title ++ ":")

/-- Recover native command-local options before selecting the shared work budget. Lean's
{lit}`set_option … in` wrapper has restored the outer scope when completed linters run. -/
private partial def commandOptions (command : Syntax) : TermElabM Options := do
  checkSystem "SQL command options"
  if command.isOfKind ``Parser.Command.in then
    let options ← if command[0].isOfKind ``Parser.Command.set_option then
        Prod.fst <$> Elab.elabSetOption command[0][1] command[0][3]
      else getOptions
    withOptions (fun _ => options) <| commandOptions command[2]
  else getOptions

/-- Register with Lean's native completed-command linter pipeline. Ordinary declaration
elaboration, including native asynchronous and mutual proofs, retains its existing handler.
Discovery, all statements in a command and native suggestions share one configured budget. -/
private def automaticLinter : Command.Linter where
  name := `Belay.Sqlite.Check.automaticLinter
  run := fun command => do
    let trees := (← getInfoState).trees
    liftTermElabM do
      let some options ← attempt (commandOptions command) | return
      unless sql.check.get options do return
      if sql.checkRecursionLimit.get options == 0 then return
      let emitted ← withOptions (fun _ => maxRecDepth.set options (sql.checkRecursionLimit.get options)) <|
        withinBudget (sql.checkBudget.get options) do
          let (statements, excluded) ← statements command trees
          for statement in statements do
            let result ← checkStatement statement excluded
            if let some result := result then reportStatement command statement result
          let state ← getThe Core.State
          return (state.messages, state.infoState)
      -- The common speculative boundary discards diagnostics. Publish the fully prepared
      -- native messages/actions only after its final resource check succeeds.
      if let some (messages, infoState) := emitted then
        modifyThe Core.State fun state => { state with messages, infoState }

initialize Command.addLinter automaticLinter

end Belay.Sqlite.Check
