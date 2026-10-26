import VerifierConformance.Case
import VerifierConformance.RunPass

set_option doc.verso true

/-! The classification of a case (ADR 0004): a case whose recorder stops at the first error
compares the pass that halts ({name}`Belay.Sqlite.Model.Conformance.classifyHaltingCase`), and a
case whose recorder runs on after an SQL error compares the passes of the model's complete
executions that continue ({name}`Belay.Sqlite.Model.Conformance.runPassAllFrom`): the native record
must match all observations of one complete execution, and never the first statement of one execution
and the second of another. Compiled testing and kernel proofs use the same classification
({lit}`checkCase`). -/

namespace Belay.Sqlite.Model.Conformance

/-- The clock of a run that continues, from the clock value of each statement: the values, and 0
beyond them, or {lean}`(none : Option Clock)` without values, so that a statement that reads the
clock ends the run. -/
def runClock (clocks : List Int) : Option Clock :=
  if clocks.isEmpty then none else some fun position => clocks.getD position 0

/-- The connection at the start of a run that continues: idle, on the database of the catalog
with the native starting tables ({name}`databaseOf`), with foreign keys as the profile sets
them, and with the counters that the record gives, or unknown counters for a record without
them (ADR 0024, D1). -/
def startConnection (profile : Profile) (catalog : Catalog) (initial : List NativeTable)
    (counters : Option Counters) : Connection :=
  { state := { database := databaseOf catalog initial, counters := counters.getD {} },
    foreignKeys := profile.foreignKeys }

/-- The deepest of two positions of disagreement: the later statement, and a known position over an
unknown one. -/
def deeperPosition : Option Nat → Option Nat → Option Nat
  | some first, some second => some (max first second)
  | some first, none => some first
  | none, second => second

/-- The verdict of a case from the verdicts of its complete executions: the case agrees when one
execution agrees; otherwise it is unsupported when one execution is unsupported; otherwise it is a
disagreement at the deepest position of the executions, so that a diagnostic names the execution
that came closest. A case with no complete execution is unsupported. For one execution it is the
verdict of that execution ({lit}`Verdict.ofExecutions_singleton`). -/
def Verdict.ofExecutions (verdicts : List Verdict) : Verdict :=
  if verdicts.contains .agree then .agree
  else if verdicts.contains .modelUnsupported then .modelUnsupported
  else match verdicts.filterMap (fun verdict => match verdict with
      | .disagree position => some position
      | .agree | .modelUnsupported => none) with
    | [] => .modelUnsupported
    | position :: positions => .disagree (positions.foldl deeperPosition position)

/-- Compare the passes of the complete executions of a case that runs on after an SQL error with its
native record, from the connection at the start of the run: {name}`classifyObserved` for each pass, and
the combined verdict ({name}`Verdict.ofExecutions`). Each pass is compared as a whole, so a record
matches an execution only when it matches all of that execution's observations. -/
def classifyPasses (c : Case) (connection : Connection) (passes : List RunPass) : Verdict :=
  Verdict.ofExecutions (passes.map fun pass =>
    classifyObserved c (observeState connection.state :: pass.observations) pass.outputs pass.possible pass.supported)

/-- Classify a case whose recorder runs on after an SQL error: resolve the schema
({name}`resolveSchema`), then compare the passes of the complete executions of the model's run that
continues ({name}`runPassAllFrom`) from {name}`startConnection` ({name}`classifyPasses`). Each statement
resolves against the connection's state when it runs, with the values that the record binds to it
({name}`bindValues`), the clock of the record's clock values ({name}`runClock`) and the counters
of the record. A statement
that ends the run makes the case unsupported. A schema restriction is unsupported; a schema that
SQLite prepared but resolution refuses is a disagreement. -/
def classifyRunCase (c : Case) : Verdict :=
  match resolveSchema c.profile c.schema with
  | .error (.schemaRestricted _) | .error (.scriptRestricted _) => .modelUnsupported
  | .error (.schemaPrepareError ..) => .disagree none
  | .ok catalog =>
    let connection := startConnection c.profile catalog c.initial c.counters
    classifyPasses c connection
      (runPassAllFrom { profile := c.profile, mode := .execution } (runClock c.clocks) 0 connection
        (bindValues c.script c.parameters))

/-- Classify a case: {name}`classifyRunCase` when its recorder ran on after an error
({lit}`Case.continues`), and {name}`classifyHaltingCase` otherwise. -/
def classifyCase (c : Case) : Verdict :=
  if c.continues then classifyRunCase c else classifyHaltingCase c

/-- Both compiled testing and concrete kernel proofs use the same classification. -/
def checkCase (c : Case) : Bool := decide (classifyCase c = .agree)

/-- For every case: if {name}`classifyCase` gives {name}`Verdict.modelUnsupported`, then
{name}`checkCase` is false. So no unsupported verdict can supply successful tier-two proof
evidence. -/
theorem unsupported_not_checked (c : Case) (h : classifyCase c = .modelUnsupported) :
    checkCase c = false := by simp [checkCase, h]

end Belay.Sqlite.Model.Conformance
