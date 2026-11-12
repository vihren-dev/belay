import Belay.Sqlite.Tooling.Counterexamples.CheckOperation

set_option doc.verso true

/-! Text for checked SQL outcomes. The checker supplies certified evidence and validated
replays; formatting this record alone does not certify any proposition. -/

namespace Belay.Sqlite.Check

open Lean Meta Belay.Sqlite.Model

/-- The lines of the database of a counterexample: {lit}`Database:` with the name of the witness
constant when it has one, as Lean names it in the current namespace, then its tables ({name}`databaseTables`). A database with no table is
{lit}`Database: empty`, or {lit}`Database: sample (no tables)` for a named one. -/
def databaseLines (text : WitnessText) : MessageData :=
  match text.name, text.tables.isEmpty with
  | none, true => "Database: empty"
  | some name, true => m!"Database: {MessageData.ofConstName name} (no tables)"
  | none, false => m!"Database:\n{text.tables}"
  | some name, false => m!"Database: {MessageData.ofConstName name}\n{text.tables}"

/-- The lines of the model outputs of one replay: one line for each statement, with the name of
the script ({name}`Replay.Report.label`, as Lean names it in the current namespace) or its first SQL line, the statement number when the
script has several statements, the parameter values ({name}`cellLiteral`) when it has some, and the
output. For example, {lit}`uniqueEmail: error 19`. A report with no original SQL gives no line. -/
def outputLines (report : Replay.Report) : List MessageData :=
  match report.original with
  | none => []
  | some original =>
    let label := match report.label with
      | some name => MessageData.ofConstName name
      | none => m!"{(original.trimAscii.toString.splitOn "\n").headD ""}"
    let several := report.outputs.length > 1
    (report.outputs.zipIdx).map fun (output, index) =>
      let number := if several then s!", statement {index + 1}" else ""
      let values := report.bindings.getD index []
      let parameters := if values.isEmpty then "" else s!" (parameters {", ".intercalate (values.map cellLiteral)})"
      m!"{label}{number}{parameters}: {repr output}"

/-- One SQLite shell script for all the replays of a counterexample. Each replay after the first
starts with {lit}`.open :memory:`, so that it runs on a new database, as the model's run does. -/
def replayScript (reports : Array Replay.Report) : String :=
  match reports.toList with
  | [] => ""
  | first :: rest => first.sqlite ++ String.join (rest.map (".open :memory:\n" ++ ·.sqlite))

/-- Describe a checked outcome. A refutation is one block: the database as tables, the
environment when it is not the default candidate, the named inputs, the failing observation,
the model output of each checked statement ({name}`outputLines`), each note, each different
database construction once, and one replay script ({name}`replayScript`). A plain Lean
predicate receives its database reconstruction. Unknown explicitly leaves the proposition
undecided, with the reason when the outcome has one ({name}`Outcome.reason`). -/
def describe (outcome : Outcome) : MetaM MessageData := do
  match outcome.result with
  | .unknown => return match outcome.reason with
    | some reason => m!"SQL check: unknown; {reason}."
    | none => "SQL check: unknown; no proof or replayable counterexample was found within the budget."
  | .proved proof => return m!"SQL check: proved.\nChecked proof: by {proof.tactic}"
  | .refuted witness _ =>
    let mut message := m!"SQL check: false."
    if let some text := outcome.witness then
      message := message ++ m!"\n{databaseLines text}"
      if let some environment := text.environment then
        message := message ++ m!"\nEnvironment: {environment}"
    for (name, value) in witness.named do
      message := message ++ m!"\n{name}: {value}"
    if let some observation := outcome.observation then
      message := message ++ m!"\nFailing observation: {observation}"
    for line in outcome.replays.toList.flatMap outputLines do
      message := message ++ m!"\n{line}"
    let notes := outcome.replays.toList.filterMap (·.note)
    for note in notes.eraseDups do
      message := message ++ m!"\nNote: {note}"
    unless outcome.replays.isEmpty do
      let constructions := (outcome.replays.toList.map (·.construction)).eraseDups
      message := message ++ m!"\nConstruction:\n{"\n".intercalate constructions}"
      message := message ++ m!"\nSQLite replay:\n{replayScript outcome.replays}"
    return message

end Belay.Sqlite.Check
