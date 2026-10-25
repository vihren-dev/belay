import Belay.Sqlite.ProofCostRecord
import Lean.Language.Basic
import Lean.Util.Trace

set_option doc.verso true

/-! Reading and removing the native body trace (ADR 0017, S7). Lean elaborates the body of a
declaration inside a trace node of the class {lit}`Elab.definition.value`. With profiling in
heartbeat mode, the node keeps the heartbeat counter at its start and its end. The collector reads
these nodes and then removes them, because Lean would print them as messages. -/

namespace Belay.Sqlite.ProofCost

open Lean Language

/-- The native trace class of a declaration body (Lean 4.34.1, {lit}`Lean/Elab/MutualDef.lean`). -/
def bodyClass : Name := `Elab.definition.value

/-- The largest counter value below which adjacent integers have distinct {lean}`Float` values. -/
def maximumExactHeartbeat : Nat := 9007199254740991

/-- One body node: the printed declaration name and the measured count. -/
structure BodyNode where
  /-- The declaration name as Lean's message printer shows it. -/
  label : String
  /-- Whether the body elaborated, and whether its count is exact. -/
  status : ProofCostStatus
  /-- The exact count, when {lit}`status` is completed. -/
  heartbeats : Option Nat

/-- The printed text of an eager name message. Lazy messages have no text without a context. -/
partial def label : MessageData → Option String
  | .ofFormatWithInfos value => some value.fmt.pretty
  | .withContext _ inner | .withNamingContext _ inner | .nest _ inner | .group inner
  | .tagged _ inner | .ofOriginatingSyntax _ inner => label inner
  | .ofWidget _ _ | .ofGoal _ | .compose _ _ | .trace _ _ _ | .ofLazy _ _ => none

/-- The printed form of a declaration name that a body node uses for it. -/
def nameLabel (name : Name) : String := (label (MessageData.ofName name)).getD name.toString

/-- The exact difference of the counters, or {lean}`none` when a {lean}`Float` endpoint cannot
represent its integer exactly. -/
def exactCount (data : TraceData) : Option Nat :=
  let (first, last) := (data.startTime, data.stopTime)
  if first >= 0 && last >= first && last <= maximumExactHeartbeat.toFloat &&
      first.toUInt64.toNat.toFloat == first && last.toUInt64.toNat.toFloat == last then
    some (last.toUInt64.toNat - first.toUInt64.toNat)
  else none

/-- The body nodes inside a message, including nested ones. -/
partial def bodyNodes : MessageData → Array BodyNode
  | .trace data message children =>
    let nested := children.foldl (fun found child => found ++ bodyNodes child) #[]
    if data.cls != bodyClass then nested else
      match label message with
      | none => nested
      | some name =>
        let heartbeats := exactCount data
        let status := if data.result? != some .success then .failed
          else if heartbeats.isNone then .precisionUnavailable else .completed
        nested.push { label := name, status, heartbeats }
  | .withContext _ inner | .withNamingContext _ inner | .nest _ inner | .group inner
  | .tagged _ inner | .ofOriginatingSyntax _ inner | .ofWidget _ inner => bodyNodes inner
  | .compose first second => bodyNodes first ++ bodyNodes second
  | .ofFormatWithInfos _ | .ofGoal _ | .ofLazy _ _ => #[]

/-- Whether a message contains a body node. -/
partial def mentionsBody : MessageData → Bool
  | .trace data _ children => data.cls == bodyClass || children.any mentionsBody
  | .withContext _ inner | .withNamingContext _ inner | .nest _ inner | .group inner
  | .tagged _ inner | .ofOriginatingSyntax _ inner | .ofWidget _ inner => mentionsBody inner
  | .compose first second => mentionsBody first || mentionsBody second
  | .ofFormatWithInfos _ | .ofGoal _ | .ofLazy _ _ => false

/-- The messages that stand for a message once its body nodes are gone. A body node is replaced by
its children: the traces of other classes that the user enabled and Lean recorded inside it. So a
trace that the user asked for stays in the output, as it is without the collector. -/
partial def withoutBodyNodesIn : MessageData → Array MessageData
  | .trace data message children =>
    let inner := children.flatMap withoutBodyNodesIn
    if data.cls == bodyClass then inner
    -- The anonymous root that Lean puts around the top-level traces of a message disappears with
    -- its last child: an empty message would print as an empty line.
    else if data.cls.isAnonymous && inner.isEmpty && !children.isEmpty then #[]
    else #[.trace data message inner]
  | .withContext context inner => (withoutBodyNodesIn inner).map (.withContext context ·)
  | .withNamingContext context inner => (withoutBodyNodesIn inner).map (.withNamingContext context ·)
  | .nest indent inner => (withoutBodyNodesIn inner).map (.nest indent ·)
  | .group inner => (withoutBodyNodesIn inner).map .group
  | .tagged tag inner => (withoutBodyNodesIn inner).map (.tagged tag ·)
  | .ofOriginatingSyntax origin inner => (withoutBodyNodesIn inner).map (.ofOriginatingSyntax origin ·)
  | .ofWidget widget inner => (withoutBodyNodesIn inner).map (.ofWidget widget ·)
  | .compose first second =>
    let join (parts : Array MessageData) := parts.foldl (fun found part => .compose found part) MessageData.nil
    #[.compose (join (withoutBodyNodesIn first)) (join (withoutBodyNodesIn second))]
  | message => #[message]

/-- The messages that replace one message: itself when it has no body node. -/
def replacementMessages (message : MessageData) : Array MessageData :=
  if mentionsBody message then withoutBodyNodesIn message else #[message]

/-- The elements of a persistent array, with each element from index {lit}`first` on replaced by
the elements that {lit}`replace` gives. Earlier elements stay. -/
def replaceFrom {α : Type} (items : PersistentArray α) (first : Nat) (replace : α → Array α) :
    PersistentArray α :=
  (items.foldl (fun (kept, index) item =>
    (if index < first then kept.push item else (replace item).foldl (·.push ·) kept, index + 1)) ({}, 0)).1

/-- The body nodes of every message and trace of a snapshot. -/
def snapshotNodes (snapshot : Snapshot) : Array BodyNode :=
  let fromTraces := snapshot.traces.traces.foldl (fun found trace => found ++ bodyNodes trace.msg) #[]
  snapshot.diagnostics.msgLog.reportedPlusUnreported.foldl
    (fun found message => found ++ bodyNodes message.data) fromTraces

/-- A snapshot without body nodes in its messages and traces. A snapshot without such a node is
returned as it is. -/
def withoutBodyNodes (snapshot : Snapshot) : BaseIO Snapshot := do
  let log := snapshot.diagnostics.msgLog
  let replaceMessage (message : Message) :=
    (replacementMessages message.data).map ({ message with data := · })
  let clean : MessageLog := { log with
    reported := replaceFrom log.reported 0 replaceMessage
    unreported := replaceFrom log.unreported 0 replaceMessage }
  let traces := replaceFrom snapshot.traces.traces 0 fun trace =>
    (replacementMessages trace.msg).map ({ trace with msg := · })
  if !(log.reportedPlusUnreported.any (mentionsBody ·.data)) &&
      !(snapshot.traces.traces.any (mentionsBody ·.msg)) then return snapshot
  return { snapshot with diagnostics := ← Snapshot.Diagnostics.ofMessageLog clean
                         traces := { snapshot.traces with traces } }

/-- A snapshot tree whose snapshots have no body nodes. The children are rebuilt when they finish,
so the elaboration stays asynchronous. -/
partial def withoutBodyNodesTree (tree : SnapshotTree) : BaseIO SnapshotTree := do
  let children ← tree.children.mapM fun child =>
    child.bindIO (cancelTk? := child.cancelTk?) (sync := true) fun inner =>
      (SnapshotTask.finished child.stx? ·) <$> withoutBodyNodesTree inner
  return { element := ← withoutBodyNodes tree.element, children }

end Belay.Sqlite.ProofCost
