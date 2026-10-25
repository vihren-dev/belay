import Belay.Sqlite.ProofCostReport
import Std.Data.HashMap

set_option doc.verso true

/-! Comparison of the proof costs of a library with a baseline file (ADR 0017, S7). The baseline
is a report that an earlier run printed with {lit}`--json`. A proof grew when its count is more than
the baseline count plus the allowance, in internal heartbeats, so no step rounds. The comparison
never turns a missing or failed count into zero: such a proof is listed in a section of its own. It
uses only records with a stable name, because a private name or an example moves with edits. -/

namespace Belay.Sqlite

open Std

/-- Why a proof of the baseline has no completed count now. -/
inductive MissingCause where
  /-- The current compile has no record and no theorem of this name; it was removed or renamed. -/
  | absent
  /-- A theorem of this name exists, but the module was compiled without the collector. -/
  | unmeasured
  /-- The body failed. -/
  | failed
  /-- The current count is not exact. -/
  | precisionUnavailable
  deriving BEq

/-- What a library's current costs say about its baseline. -/
structure LibraryComparison where
  /-- The name of the library. -/
  name : String
  /-- Proofs that grew by more than the allowance, as baseline and current record. -/
  growth : Array (ProofCostRecord × ProofCostRecord) := #[]
  /-- Pairs of records that were made by different compilers, schemes or units. -/
  incompatible : Array (ProofCostRecord × ProofCostRecord) := #[]
  /-- Baseline proofs with no completed record now. -/
  missing : Array (ProofCostRecord × MissingCause) := #[]
  /-- Records that failed and have no baseline entry. -/
  failed : Array ProofCostRecord := #[]
  /-- Proofs with a stable name that the baseline does not have. -/
  added : Array ProofCostRecord := #[]
  /-- Baseline records with no completed count. They cannot be compared. -/
  unusableBaseline : Array ProofCostRecord := #[]

/-- Whether two records measure the same thing, so that their counts can be compared. -/
def ProofCostRecord.comparableWith (first second : ProofCostRecord) : Bool :=
  first.compiler == second.compiler && first.scheme == second.scheme && first.unit == second.unit

/-- Whether a record takes part in the comparison. -/
private def ProofCostRecord.isStable (record : ProofCostRecord) : Bool := record.identity == .stable

/-- Compare the current costs of one library with its baseline. The allowance is in internal
heartbeats. -/
def compareLibrary (allowance : Nat) (baseline : Option LibraryCosts) (current : LibraryCosts) :
    LibraryComparison :=
  let key (record : ProofCostRecord) := (record.module, record.declaration)
  let now : HashMap (String × String) ProofCostRecord :=
    current.records.foldl (fun found record => if record.isStable then found.insert (key record) record else found) {}
  let before := (baseline.map (·.records)).getD #[] |>.filter (·.isStable)
  let known : HashMap (String × String) Unit :=
    before.foldl (fun found record => found.insert (key record) ()) {}
  let unmeasured := current.unmeasured.map fun item => (item.module, item.declaration)
  let start : LibraryComparison := { name := current.name }
  let compared := before.foldl (fun found old =>
    match old.status, old.heartbeats with
    | .completed, some oldCount =>
      match now[key old]? with
      | none =>
        let cause := if unmeasured.contains (key old) then .unmeasured else .absent
        { found with missing := found.missing.push (old, cause) }
      | some new =>
        if !old.comparableWith new then { found with incompatible := found.incompatible.push (old, new) }
        else match new.status, new.heartbeats with
          | .completed, some newCount =>
            if newCount > oldCount + allowance then { found with growth := found.growth.push (old, new) } else found
          | .failed, _ => { found with missing := found.missing.push (old, .failed) }
          | _, _ => { found with missing := found.missing.push (old, .precisionUnavailable) }
    | _, _ => { found with unusableBaseline := found.unusableBaseline.push old }) start
  current.records.foldl (fun found record =>
    if !record.isStable || known.contains (key record) then found
    else if record.status == .failed then { found with failed := found.failed.push record }
    else if record.status == .completed then { found with added := found.added.push record }
    else found) compared

/-- Compare every selected library with the baseline library of the same name. A library that the
baseline does not have has only added proofs. -/
def compareCosts (allowance : Nat) (baseline current : Array LibraryCosts) : Array LibraryComparison :=
  current.map fun library => compareLibrary allowance (baseline.find? (·.name == library.name)) library

/-- The exit code of a comparison: 2 when some records are incompatible, 1 when a proof grew, has no
completed count or failed, and 0 otherwise. Proofs that were added do not change the code. -/
def comparisonExit (comparisons : Array LibraryComparison) : UInt32 :=
  if comparisons.any (!·.incompatible.isEmpty) then 2
  else if comparisons.any fun item => !item.growth.isEmpty || !item.missing.isEmpty || !item.failed.isEmpty then 1
  else 0

/-- The text of a count: the units, or a word when there is none. -/
private def countText (record : ProofCostRecord) : String :=
  match record.heartbeats with
  | some heartbeats => showUnits heartbeats
  | none => "none"

/-- The sentence that says why a baseline proof has no completed count. -/
private def causeText : MissingCause → String
  | .absent => "no such theorem now; it was removed or renamed"
  | .unmeasured => "the module was compiled without collection"
  | .failed => "the body failed"
  | .precisionUnavailable => "the count is not exact"

/-- The text of the comparison of one library. -/
def LibraryComparison.render (comparison : LibraryComparison) (allowance : Nat) : String :=
  let section_ (title : String) (lines : Array String) : List String :=
    if lines.isEmpty then [] else title :: lines.toList
  let name (record : ProofCostRecord) := s!"  {record.module}  {record.declaration}"
  let lines := [s!"Library {comparison.name}: compared with the baseline, allowance {showUnits allowance}"]
    ++ section_ "Grew by more than the allowance:" (comparison.growth.map fun (old, new) =>
        s!"{name new}  {countText old} -> {countText new}")
    ++ section_ "Not comparable, made by another compiler, scheme or unit:" (comparison.incompatible.map fun (old, new) =>
        s!"{name new}  baseline: Lean {old.compiler}, {old.scheme}, {old.unit}; now: Lean {new.compiler}, {new.scheme}, {new.unit}")
    ++ section_ "In the baseline, with no completed count now:" (comparison.missing.map fun (old, cause) =>
        s!"{name old}  {countText old}: {causeText cause}")
    ++ section_ "Failed, not in the baseline:" (comparison.failed.map name)
    ++ section_ "Added, not in the baseline:" (comparison.added.map fun record => s!"{name record}  {countText record}")
    ++ section_ "In the baseline without a completed count, not compared:" (comparison.unusableBaseline.map name)
  "\n".intercalate lines

end Belay.Sqlite
