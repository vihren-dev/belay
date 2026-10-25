import Belay.Sqlite.ProofCostTrace
import Belay.Sqlite.SqlSourceRecord

set_option doc.verso true

/-! The option, the unfinished work and the extension of the proof-cost collector
(ADR 0017, S7). A command that starts asynchronous proofs returns before they finish, so the
collector keeps the proof tasks and reads their body nodes when the module is written. They are
in their own module because Lean cannot run an {lit}`initialize` declaration in the module that
defines it, and the handlers use both. -/

namespace Belay.Sqlite.ProofCost

open Lean Language

/-- Collect the cost of proof bodies in this scope. The default is false, so importing the
collector changes nothing until a user opts in. -/
register_option belay.proofCosts : Bool := {
  defValue := false
  descr := "measure the completed body elaboration of named proofs" }

/-- A declaration that a command introduced, as the body node will name it. -/
structure Declared where
  /-- The printed name, see {lean}`nameLabel`. -/
  label : String
  /-- The kind of the proof. -/
  kind : ProofCostKind
  /-- How stable the name is. -/
  identity : ProofCostIdentity

/-- The work of one command that is not complete when the command returns: the body nodes it
already has, the asynchronous proof tasks it started, and what the command declared. -/
structure Pending where
  /-- The module being compiled. -/
  module : String
  /-- The hash of the module source, see {lean}`sqlTextHash`. -/
  sourceHash : UInt64
  /-- The source offset of the command, which names anonymous examples. -/
  offset : Nat
  /-- Whether proofs elaborate asynchronously ({lit}`Elab.async`). -/
  asynchronous : Bool
  /-- The proofs and proof-valued definitions that the command declared. -/
  declared : Array Declared
  /-- Body nodes that were available when the command returned. -/
  immediate : Array BodyNode
  /-- The body nodes of proof tasks that may finish later. A task keeps only these nodes, so the
  snapshot trees of the proofs can be freed when Lean has reported them. -/
  tasks : Array (Task (Array BodyNode))
  deriving Inhabited

/-- Whether a body node belongs to an anonymous example. -/
def isExampleLabel (label : String) : Bool := label == "_example" || label.endsWith "._example"

/-- The record for one body node, or none when the node is not a named proof or example. -/
def Pending.record? (pending : Pending) (node : BodyNode) : Option ProofCostRecord :=
  let scheme := s!"proof-body-v1-{if pending.asynchronous then "async" else "sync"}"
  let make (declaration : String) (kind : ProofCostKind) (identity : ProofCostIdentity) :=
    { module := pending.module, declaration, kind, identity, status := node.status,
      heartbeats := node.heartbeats, scheme, sourceHash := pending.sourceHash }
  match pending.declared.find? (·.label == node.label) with
  | some declared => some (make node.label declared.kind declared.identity)
  | none => if isExampleLabel node.label
      then some (make s!"{node.label}@{pending.offset}" .anonymousExample .anonymous) else none

/-- Every record of a command, in an order that does not depend on task timing. The caller must
run this only when the tasks are complete. -/
def Pending.records (pending : Pending) : Array ProofCostRecord :=
  let nodes := pending.tasks.foldl (fun found task => found ++ task.get) pending.immediate
  nodes.filterMap pending.record?

/-- The records of a module without repeats: a command that another handler runs again through
{lit}`elabCommand` appears in two pending entries, and a name is measured once. -/
def distinctRecords (pendings : Array Pending) : Array ProofCostRecord :=
  let all := pendings.foldl (fun found pending => found ++ pending.records) #[]
  let (_, distinct) := all.foldl (fun (seen, kept) record =>
    if seen.contains record.declaration then (seen, kept)
    else (seen.insert record.declaration, kept.push record)) ((∅ : Std.HashSet String), #[])
  distinct.qsort fun first second => first.declaration < second.declaration

/-- The records of this module. Entries hold unfinished tasks while the module compiles; only the
finished, plain records are written to the compiled file. -/
initialize costExtension : PersistentEnvExtension ProofCostRecord Pending (Array Pending) ←
  registerPersistentEnvExtension {
    name := proofCostExtensionName
    mkInitial := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn := fun pendings pending => pendings.push pending
    exportEntriesFn := distinctRecords }

end Belay.Sqlite.ProofCost
