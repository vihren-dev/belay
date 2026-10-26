import Belay.Sqlite.CheckOperation

set_option doc.verso true

/-! Text for checked SQL outcomes. The checker supplies certified evidence and validated
replays; formatting this record alone does not certify any proposition. -/

namespace Belay.Sqlite.Check

open Lean Meta

/-- Describe a checked outcome, including the actual named inputs, environment and original
SQL replay for a refutation. A plain Lean predicate receives its database reconstruction.
Unknown explicitly leaves the proposition undecided. -/
def describe (outcome : Outcome) : MetaM MessageData := do
  match outcome.result with
  | .unknown => return "SQL check: unknown; no proof or replayable counterexample was found within the budget."
  | .proved proof => return m!"SQL check: proved.\nChecked proof: by {proof.tactic}"
  | .refuted witness _ =>
    let mut message := m!"SQL check: false.\nDatabase: {witness.database}\nEnvironment: {witness.environment}"
    for (name, value) in witness.named do
      message := message ++ m!"\n{name}: {value}"
    for report in outcome.replays do
      message := message ++ m!"\nDatabase construction:\n{report.construction}"
      if report.original.isSome then
        message := message ++ m!"\nBindings: {repr report.bindings}\nModel outputs: {repr report.outputs}"
      message := message ++ m!"\nSQLite replay:\n{report.sqlite}"
    return message

end Belay.Sqlite.Check
