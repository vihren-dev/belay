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

/-- The elements of a persistent array without those that fail the test, from index {lit}`first`
on; earlier elements stay. -/
def keepFrom {α : Type} (items : PersistentArray α) (first : Nat) (keep : α → Bool) :
    PersistentArray α :=
  (items.foldl (fun (kept, index) item =>
    (if index < first || keep item then kept.push item else kept, index + 1)) ({}, 0)).1

/-- The body nodes of every message and trace of a snapshot. -/
def snapshotNodes (snapshot : Snapshot) : Array BodyNode :=
  let fromTraces := snapshot.traces.traces.foldl (fun found trace => found ++ bodyNodes trace.msg) #[]
  snapshot.diagnostics.msgLog.reportedPlusUnreported.foldl
    (fun found message => found ++ bodyNodes message.data) fromTraces

/-- A snapshot without the messages and traces that contain a body node. A snapshot without
such a message is returned as it is. -/
def withoutBodyNodes (snapshot : Snapshot) : BaseIO Snapshot := do
  let log := snapshot.diagnostics.msgLog
  let clean : MessageLog := { log with
    reported := keepFrom log.reported 0 (!mentionsBody ·.data)
    unreported := keepFrom log.unreported 0 (!mentionsBody ·.data) }
  let traces := keepFrom snapshot.traces.traces 0 (!mentionsBody ·.msg)
  if clean.reported.size == log.reported.size && clean.unreported.size == log.unreported.size &&
      traces.size == snapshot.traces.traces.size then return snapshot
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
