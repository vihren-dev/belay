import Belay.Sqlite.ProofCostUnits

set_option doc.verso true

/-! The proof-cost report of one invocation of the checker (ADR 0017, S7), built from what the
compiled modules of a library stored. The module is pure, so tests can run it without Lake and
without compiled libraries. The JSON form of the report is also the baseline file that a later
invocation compares with. -/

namespace Belay.Sqlite

open Lean

/-- What the checker read from one compiled module of a library. -/
structure ModuleCosts where
  /-- The module name. -/
  module : String
  /-- The records that the module stored. A module compiled without the collector has none. -/
  records : Array ProofCostRecord
  /-- The names of the theorems that the author wrote in the module, without the declarations that
  Lean generates. -/
  theorems : Array String
  /-- Whether the Lean file of the module has changed since the compiled file was made. Only a
  module with records can tell. -/
  stale : Bool
  deriving Inhabited

/-- A theorem that the report cannot give a completed count. -/
structure Unmeasured where
  /-- The module that declares the theorem. -/
  module : String
  /-- The qualified name of the theorem. -/
  declaration : String
  deriving BEq, Inhabited, ToJson, FromJson

/-- The proof costs of one library, in the order the report shows them. -/
structure LibraryCosts where
  /-- The name of the library. -/
  name : String
  /-- Every record of the library's modules, by module and then declaration. -/
  records : Array ProofCostRecord
  /-- The theorems without a completed record, by module and then declaration. -/
  unmeasured : Array Unmeasured
  /-- The modules whose Lean file changed after the compiled file was made. -/
  stale : Array String
  deriving Inhabited, ToJson, FromJson

/-- The costs of a library from its modules: each theorem without a completed record is
unmeasured, and a module with a changed source is stale. -/
def LibraryCosts.ofModules (name : String) (modules : Array ModuleCosts) : LibraryCosts :=
  let sorted := modules.qsort (·.module < ·.module)
  { name
    records := sorted.foldl (fun found module =>
      found ++ module.records.qsort (·.declaration < ·.declaration)) #[]
    unmeasured := sorted.foldl (fun found module =>
      let completed := module.records.filter (·.status == .completed) |>.map (·.declaration)
      let missing := (module.theorems.filter (!completed.contains ·)).qsort (· < ·)
      found ++ missing.map ({ module := module.module, declaration := · })) #[]
    stale := (sorted.filter (·.stale)).map (·.module) }

/-- The report as the baseline file: the unit, and the costs of each library. -/
def costsJson (libraries : Array LibraryCosts) : Json :=
  Json.mkObj [("unit", toJson proofCostUnit), ("internalUnitsPerBudgetUnit", toJson heartbeatsPerBudgetUnit),
    ("libraries", toJson libraries)]

/-- Read costs back from a baseline file. -/
def costsOfJson (json : Json) : Except String (Array LibraryCosts) := do
  let libraries ← json.getObjVal? "libraries"
  fromJson? libraries

/-- One line of the table of records. -/
private def recordLine (record : ProofCostRecord) : String :=
  let kind := match record.kind with
    | .thm => "theorem" | .proofDefinition => "definition" | .anonymousExample => "example"
  let count := match record.status, record.heartbeats with
    | .completed, some heartbeats => showUnits heartbeats
    | .failed, _ => "failed"
    | .completed, none | .precisionUnavailable, _ => "not exact"
  s!"  {record.module}  {kind}  {record.declaration}  {count}"

/-- The text of the report for one library. -/
def LibraryCosts.render (library : LibraryCosts) : String :=
  let stable := library.records.filter (·.identity == .stable)
  let unstable := library.records.filter (·.identity != .stable)
  let section_ (title : String) (lines : Array String) : List String :=
    if lines.isEmpty then [] else title :: lines.toList
  let lines := [s!"Library {library.name}: {stable.size} measured proofs"] ++ (stable.map recordLine).toList
    ++ section_ "Unstable names, which a baseline does not compare (private names and examples):"
        (unstable.map recordLine)
    ++ section_ "Theorems without a completed count:"
        (library.unmeasured.map fun item => s!"  {item.module}  {item.declaration}")
    ++ section_ "Modules whose source changed after they were compiled; run lake build and check again:"
        (library.stale.map (s!"  " ++ ·))
  "\n".intercalate lines

/-- The text of the report for all selected libraries, with what the counts mean. -/
def renderCosts (libraries : Array LibraryCosts) : String :=
  let pairs := libraries.foldl (fun found library => library.records.foldl (fun found record =>
    let pair := s!"Lean {record.compiler}, {record.scheme}"
    if found.contains pair then found else found.push pair) found) #[]
  let header := [s!"Proof costs in Lean budget units (1 unit = {heartbeatsPerBudgetUnit} internal heartbeats).",
    "A count is the completed body elaboration of one named theorem or proof-valued definition.",
    "It excludes the statement, the kernel check, proofs inside other declarations and declarations",
    "that Lean generates. A definition appears only if collection was on when it was compiled.",
    s!"Data from: {", ".intercalate pairs.toList}."]
  "\n".intercalate (header ++ (libraries.map (·.render)).toList)

end Belay.Sqlite
