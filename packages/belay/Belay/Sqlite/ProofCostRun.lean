import Belay.Sqlite.ProofCostArguments
import Belay.Sqlite.ProofCostCompare
import Belay.Sqlite.ProofCostModuleData

set_option doc.verso true

/-! The {lit}`--costs` mode of {lit}`lake exe belay-sql-check` (ADR 0017, S7). The checker lists the
modules of each selected library with their compiled and source files; this module reads them and
prints the report or the comparison. It never builds, and it never writes a file, so the baseline
stays as the user saved it. -/

namespace Belay.Sqlite

open Lean System

/-- A module of a selected library with the files that the checker needs. -/
structure ModuleFiles where
  /-- The module name. -/
  name : String
  /-- The compiled file. -/
  olean : FilePath
  /-- The Lean file that the module is compiled from. -/
  source : FilePath

/-- Read the costs of one library. A module that cannot be read is a problem, because the library then
has no evidence about it. -/
def libraryCosts (name : String) (modules : Array ModuleFiles) : IO (LibraryCosts × Array String) := do
  let mut read : Array ModuleCosts := #[]
  let mut problems : Array String := #[]
  for module in modules do
    if !(← module.olean.pathExists) then
      problems := problems.push s!"library {name}: module {module.name} has no compiled file {module.olean}; run lake build {name} to compile it"
      continue
    try read := read.push (← readModuleCosts module.name module.olean module.source)
    catch error =>
      problems := problems.push s!"library {name}: cannot read the compiled module {module.name}: {error}; delete its files in the build folder and run lake build {name}"
  let costs := LibraryCosts.ofModules name read
  let stale := costs.stale.map fun module =>
    s!"library {name}: module {module} changed after it was compiled, so its counts may not describe the file; run lake build {name} and check again"
  return (costs, problems ++ stale)

/-- Read a baseline file, or say what to change. -/
def readBaseline (file : String) : IO (Except String (Array LibraryCosts)) := do
  let advice := s!"; create it with lake exe belay-sql-check --costs --json > {file}"
  unless ← (FilePath.mk file).pathExists do return .error s!"the baseline {file} does not exist{advice}"
  let text ← try IO.FS.readFile file catch error =>
    return .error s!"the baseline {file} cannot be read: {error}{advice}"
  match Json.parse text with
  | .error message => return .error s!"the baseline {file} is not JSON: {message}{advice}"
  | .ok json => return (costsOfJson json).mapError fun message => s!"the baseline {file} has an unexpected shape: {message}{advice}"

/-- Print the costs or the comparison for the selected libraries. The result is the exit code: 0 for a
report or a comparison without findings, 1 for growth or for a proof without a completed count, and
2 for incompatible records, a baseline that cannot be used, and libraries that cannot be read. -/
def runCosts (libraries : Array (String × Array ModuleFiles)) (settings : CostSettings) : IO UInt32 := do
  let mut costs : Array LibraryCosts := #[]
  let mut problems : Array String := #[]
  for (name, modules) in libraries do
    let (found, trouble) ← libraryCosts name modules
    costs := costs.push found
    problems := problems ++ trouble
  let mut code : UInt32 := 0
  match settings.baseline, settings.allowance with
  | some file, some allowance =>
    match ← readBaseline file with
    | .error message => problems := problems.push message
    | .ok baseline =>
      let comparisons := compareCosts allowance baseline costs
      for comparison in comparisons do IO.println (comparison.render allowance)
      code := comparisonExit comparisons
  | _, _ => IO.println (if settings.json then (costsJson costs).pretty else renderCosts costs)
  for problem in problems do IO.eprintln s!"error: {problem}"
  return if problems.isEmpty then code else 2

end Belay.Sqlite
