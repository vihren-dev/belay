import Lean.Linter.Util
import Belay.Sqlite.CheckBudget

set_option doc.verso true

/-! Native completed declaration information identifies the original closed statements.
Saved environments retain anonymous examples; proof-body local contexts are never imported. -/

namespace Belay.Sqlite.Check
open Lean Meta Elab Term

/-- A completed theorem statement and its original source context. The closed type includes
all section hypotheses that Lean retained, including those used only by the proof. -/
structure Statement where
  /-- The declaration being checked; its name is excluded from all certificates. -/
  name : Name
  /-- The original closed proposition, rather than the proof body or a local goal. -/
  proposition : Expr
  /-- The native saved environment/options for this declaration, including anonymous examples. -/
  context : ContextInfo
  /-- The declaration binder or anonymous statement range used for diagnostics. -/
  ref : Syntax

/-- Discovery data from native information nodes, before their completed types are selected. -/
private structure Discovery where
  /-- Every named binder or body declaration introduced in this command is excluded. -/
  names : Array Name := #[]
  /-- Binder source references identify named statements independently of proof syntax. -/
  references : Array (Name × Syntax) := #[]
  /-- Saved native body contexts supply names and environments, never proof evidence. -/
  bodies : Array (Name × ContextInfo × Syntax) := #[]

/-- Collect completed theorem types from native information trees. The traversal checks
cancellation at each information node. Mutual peers and generated body declarations join
the exclusion set. Other definitions are not checked. Anonymous examples are recognized by their native declaration binder at the {lit}`example` keyword
and a closed proposition type; they use their
saved environment even though Lean removes them from the ordinary command environment. -/
def statements (command : Syntax) (trees : PersistentArray InfoTree) :
    TermElabM (Array Statement × Array Name) := do
  let mut found : Discovery := {}
  for tree in trees do
    found ← tree.foldInfoM (init := found) fun context info found => do
      checkSystem "SQL statement discovery"
      let mut found := found
      if let .ofTermInfo termInfo := info then
        if termInfo.isBinder && termInfo.expr.isConst then
          let name := termInfo.expr.constName!
          found := { found with
            names := found.names.push name
            references := found.references.push (name, termInfo.stx) }
      if (Term.getBodyInfo? info).isSome then
        if let some name := context.parentDecl? then
          found := { found with
            names := found.names.push name
            bodies := found.bodies.push (name, context, info.stx) }
      return found
  let currentEnvironment ← getEnv
  let mut result : Array Statement := #[]
  for (name, context, body) in found.bodies do
    if result.any (·.name == name) then continue
    let environment := if context.env.contains name then context.env
      else context.cmdEnv?.getD currentEnvironment
    let some declaration := environment.find? name | continue
    let anonymous := command.find? fun node =>
      node.getKind == ``Parser.Command.example && node[0].getRange?.isSome &&
        found.references.any (fun entry => entry.1 == name &&
          entry.2.getRange? == node[0].getRange?)
    unless declaration matches .thmInfo _ do
      unless anonymous.isSome && (← withEnv environment <| isProp declaration.type) do continue
    let ref := (found.references.find? (·.1 == name)).map (·.2) |>.getD
      (Syntax.ofRange { start := command.getPos?.getD 0, stop := body.getPos?.getD 0 })
    result := result.push {
      name
      proposition := declaration.type
      context := { context with env := environment }
      ref }
  return (result, found.names)

end Belay.Sqlite.Check
