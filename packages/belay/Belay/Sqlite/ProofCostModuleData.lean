import Lean
import Belay.Sqlite.ProofCostReport
import Belay.Sqlite.SqlSourceRecord

set_option doc.verso true

/-! Reading proof costs from a compiled module (ADR 0017, S7). The checker reads the module file
and runs no elaboration. It takes the stored records, the theorems that the author wrote, and a
comparison of the module's Lean file with the text that the collector hashed. This module needs no
Lake: the checker gives it the paths. -/

namespace Belay.Sqlite

open Lean System

/-- The records of one module's entry array, as the elaborator stored them. -/
private unsafe def decodeRecordsUnsafe (entries : Array EnvExtensionEntry) : Array ProofCostRecord :=
  unsafeCast entries

/-- Read the stored records. Only the extension {lean}`proofCostExtensionName` stores values of this type. -/
@[implemented_by decodeRecordsUnsafe]
private opaque decodeRecords (entries : Array EnvExtensionEntry) : Array ProofCostRecord

/-- The declaration ranges of one module's entry array, as Lean stored them. -/
private unsafe def decodeRangesUnsafe (entries : Array EnvExtensionEntry) : Array (Name × DeclarationRanges) :=
  unsafeCast entries

/-- Read the stored ranges. Only {lit}`Lean.declRangeExt` stores values of this type. -/
@[implemented_by decodeRangesUnsafe]
private opaque decodeRanges (entries : Array EnvExtensionEntry) : Array (Name × DeclarationRanges)

/-- Whether one source range contains another, and they are not the same range. -/
private def encloses (outer inner : DeclarationRange) : Bool :=
  let before (first second : Position) := first.line < second.line || (first.line == second.line && first.column ≤ second.column)
  before outer.pos inner.pos && before inner.endPos outer.endPos &&
    (outer.pos != inner.pos || outer.endPos != inner.endPos)

/-- The names of the declarations that no other declaration of the module encloses. A theorem in a
{lit}`where` or {lit}`let rec` clause is inside the range of its parent, and belongs to its record. -/
private def outermost (ranges : Array (Name × DeclarationRanges)) : NameSet :=
  ranges.foldl (fun kept (name, own) =>
    if ranges.any fun (other, outer) => other != name && encloses outer.range own.range then kept
    else kept.insert name) {}

/-- The theorems that the author wrote: a theorem with a declaration range that no other range
encloses. Lean stores no range for the equation lemmas, size lemmas and other theorems that it
generates. -/
private def writtenTheorems (data : ModuleData) : Array String :=
  let ranges := match data.entries.find? (·.1 == `Lean.declRangeExt) with
    | some (_, entries) => decodeRanges entries
    | none => #[]
  let written := outermost ranges
  (data.constNames.zip data.constants).filterMap fun (name, info) =>
    match info with
    | .thmInfo _ => if written.contains name then some name.toString else none
    | .axiomInfo _ | .defnInfo _ | .opaqueInfo _ | .quotInfo _ | .inductInfo _ | .ctorInfo _ | .recInfo _ => none

/-- Read the compiled module {lit}`olean`. The Lean file {lit}`source` is the file that the module
was compiled from; it tells whether the records are stale. A module without records cannot be stale. -/
def readModuleCosts (module : String) (olean source : FilePath) : IO ModuleCosts := do
  let (data, _) ← readModuleData olean
  let records := match data.entries.find? (·.1 == proofCostExtensionName) with
    | some (_, entries) => decodeRecords entries
    | none => #[]
  let stale ← if records.isEmpty then pure false else
    if ← source.pathExists then
      let current := sqlTextHash (← IO.FS.readFile source)
      pure (records.any (·.sourceHash != current))
    else pure true
  return { module, records, theorems := writtenTheorems data, stale }

end Belay.Sqlite
