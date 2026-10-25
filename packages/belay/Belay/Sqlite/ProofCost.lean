import Lean
import Belay.Sqlite.ProofCostPending

set_option doc.verso true

/-! The optional proof-cost collector (ADR 0017, S7). Import this module to install it. It
measures the completed body elaboration of named theorems and of definitions whose value is a
proof, for ordinary declarations and for native {lit}`mutual` blocks, and stores one
{lean}`Belay.Sqlite.ProofCostRecord` for each in the compiled module.

To use it, import {lit}`Belay.Sqlite.ProofCost` and set {lit}`belay.proofCosts` to true: with
{lit}`set_option` in a file, or for a whole Lake library with
{lit}``leanOptions := #[⟨`weak.belay.proofCosts, true⟩]``. With the option
off, the two handlers hand the command to the next handler and change nothing. The collector never
changes how Lean elaborates: it enables Lean's own body trace, reads it, and removes it from the
output. -/

namespace Belay.Sqlite.ProofCost

open Lean Elab Command Language Meta

/-- The options that make Lean keep the body node and nothing else: the threshold removes every
other profiler node. -/
def measuringOptions (options : Options) : Options :=
  let options := options.setBool `trace.profiler true
  let options := options.setBool `trace.profiler.useHeartbeats true
  let options := options.setBool `trace.Elab.definition.value true
  trace.profiler.threshold.set options maximumExactHeartbeat

/-- Run the handlers that Lean would run if this one were absent: those registered before this
one, in Lean's order. A handler that does not know the syntax passes it on, as in Lean's own
loop. -/
private def runLater (own : Name) (stx : Syntax) : CommandElabM Unit := do
  let entries := commandElabAttribute.getEntries (← getEnv) stx.getKind
  go ((entries.dropWhile (·.declName != own)).drop 1)
where
  go : List (KeyedDeclsAttribute.AttributeEntry CommandElab) → CommandElabM Unit
    | [] => throwUnsupportedSyntax
    | entry :: rest => do
      let saved ← get
      catchInternalId unsupportedSyntaxExceptionId
        (withoutCommandIncrementality (!(← isIncrementalElab entry.declName)) (entry.value stx))
        fun _ => do set saved; go rest

/-- Whether a new constant is a theorem or a definition of a proof, and how stable its name is. -/
private def classify (info : AsyncConstantInfo) : CommandElabM (Option Declared) := do
  let name := info.name
  let identity := if isPrivateName name then ProofCostIdentity.privateName else .stable
  let declared (kind : ProofCostKind) := some { label := nameLabel name, kind, identity }
  match info.kind with
  | .thm => return declared .thm
  | .defn => return if ← liftTermElabM (isProp info.sig.get.type) then declared .proofDefinition else none
  | .axiom | .opaque | .quot | .induct | .ctor | .recursor => return none

/-- The constants of the current module, in elaboration order. The info trees of an asynchronous
theorem are not complete when the command ends, so the constants are the source of the names. -/
private def localConstants : CommandElabM (Array AsyncConstantInfo) :=
  return (← (← getEnv).getLocalConstantInfos (skipTheoremSubDecls := true))

/-- The sizes of the command state before a command, to find what the command added. -/
private structure Marks where
  /-- The number of trace elements. -/
  traces : Nat
  /-- The number of snapshot tasks. -/
  tasks : Nat
  /-- The number of constants. -/
  constants : Nat

/-- Take the body nodes that the command added, and remove them from the output: from the trace
state, and from the messages and traces of the proof tasks. Lean would print them otherwise. -/
private def hideBodyNodes (marks : Marks) :
    CommandElabM (Array BodyNode × Array (Task (Array BodyNode))) := do
  let state ← get
  let immediate := (state.traceState.traces.toArray.extract marks.traces state.traceState.traces.size).foldl
    (fun found trace => found ++ bodyNodes trace.msg) #[]
  let added := state.snapshotTasks.extract marks.tasks state.snapshotTasks.size
  let later := added.map fun task => task.task.map fun tree =>
    tree.getAll.foldl (fun found snapshot => found ++ snapshotNodes snapshot) #[]
  let hidden ← added.mapM fun task =>
    task.bindIO (cancelTk? := task.cancelTk?) (sync := true) fun tree =>
      (SnapshotTask.finished task.stx? ·) <$> withoutBodyNodesTree tree
  modify fun state => { state with
    traceState := { state.traceState with
      traces := replaceFrom state.traceState.traces marks.traces fun trace =>
        (replacementMessages trace.msg).map ({ trace with msg := · }) }
    snapshotTasks := state.snapshotTasks.extract 0 marks.tasks ++ hidden }
  return (immediate, later)

/-- Run a command with the body trace on, then record its unfinished proof work. With the option
off, the command goes straight to the next handler. -/
private def measured (own : Name) : CommandElab := fun stx => do
  unless belay.proofCosts.get (← getOptions) do return (← runLater own stx)
  let state ← get
  let marks : Marks := { traces := state.traceState.traces.size, tasks := state.snapshotTasks.size,
                         constants := (← localConstants).size }
  let failure ← try
      withScope (fun scope => { scope with opts := measuringOptions scope.opts }) (runLater own stx)
      pure none
    catch error => pure (some error)
  let (immediate, tasks) ← hideBodyNodes marks
  if let some error := failure then throw error
  let constants ← localConstants
  let declared ← (constants.extract marks.constants constants.size).filterMapM classify
  let sourceHash := sqlTextHash (← read).fileMap.source
  let asynchronous := Elab.async.get (← getOptions)
  modifyEnv fun env => costExtension.addEntry env {
    module := env.mainModule.toString, sourceHash, offset := (stx.getPos?.getD 0).byteIdx,
    asynchronous, declared, immediate, tasks }

/-- Measure ordinary declarations: theorems, definitions, instances and examples. -/
@[command_elab Lean.Parser.Command.declaration, incremental]
def elabDeclarationMeasured : CommandElab :=
  measured `Belay.Sqlite.ProofCost.elabDeclarationMeasured

/-- Measure the declarations of a native {lit}`mutual` block. -/
@[command_elab Lean.Parser.Command.mutual, incremental]
def elabMutualMeasured : CommandElab :=
  measured `Belay.Sqlite.ProofCost.elabMutualMeasured

end Belay.Sqlite.ProofCost
