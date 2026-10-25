import Belay.Sqlite.ProofCostUnits

set_option doc.verso true

/-! The command line of {lit}`lake exe belay-sql-check` (ADR 0017, S7). The tool has two modes. Without
{lit}`--costs` it checks the SQL files that the libraries read. With {lit}`--costs` it reports proof
costs and, with a baseline, compares them. One invocation has one mode. -/

namespace Belay.Sqlite

/-- The settings of the {lit}`--costs` mode. -/
structure CostSettings where
  /-- Print the report as JSON, which is also the baseline file. -/
  json : Bool := false
  /-- The baseline file to compare with. -/
  baseline : Option String := none
  /-- The allowance of growth in internal heartbeats. -/
  allowance : Option Nat := none

/-- What one invocation of the tool does. -/
inductive CheckCommand where
  /-- Compare the SQL files that the libraries read with the files on disk. -/
  | sqlFiles (library : Option String)
  /-- Report proof costs of the libraries, or compare them with a baseline. -/
  | costs (library : Option String) (settings : CostSettings)

/-- The usage text, which an argument error repeats. -/
def usage : String :=
  "usage: lake exe belay-sql-check [--library NAME]\n" ++
  "       lake exe belay-sql-check --costs [--library NAME] [--json | --baseline FILE --allowance UNITS]"

/-- Read the arguments, or say what to change. -/
def parseArguments (arguments : List String) : Except String CheckCommand := do
  let costs := arguments.contains "--costs"
  let rec go (rest : List String) (library : Option String) (settings : CostSettings) :
      Except String (Option String × CostSettings) :=
    match rest with
    | [] => .ok (library, settings)
    | "--costs" :: more => go more library settings
    | "--library" :: name :: more => go more (some name) settings
    | "--json" :: more => go more library { settings with json := true }
    | "--baseline" :: file :: more => go more library { settings with baseline := some file }
    | "--allowance" :: units :: more => do
      go more library { settings with allowance := some (← parseUnits units) }
    | other :: _ => .error s!"unexpected argument {other}\n{usage}"
  let (library, settings) ← go arguments none {}
  if !costs then
    if settings.json || settings.baseline.isSome || settings.allowance.isSome then
      throw s!"--json, --baseline and --allowance work only with --costs\n{usage}"
    return .sqlFiles library
  if settings.baseline.isSome && settings.allowance.isNone then
    throw "--baseline needs --allowance UNITS; write the growth in Lean budget units that a proof may have, for example 0 or 2.5"
  if settings.allowance.isSome && settings.baseline.isNone then
    throw "--allowance needs --baseline FILE; the allowance is the growth that a comparison accepts"
  if settings.json && settings.baseline.isSome then
    throw "--json prints the report that serves as a baseline, so it cannot be combined with --baseline; run the two modes separately"
  return .costs library settings

end Belay.Sqlite
