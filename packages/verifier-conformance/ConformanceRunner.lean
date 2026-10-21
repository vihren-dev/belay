import VerifierConformance.Predict

/-! Bounded-by-caller JSON-lines transport for the ADR 0004 compiled model.
--emit-lean serializes the decoded case as a closed term for kernel regression checks.
--predict reads ADR 0011 prediction inputs and writes the model's predictions. -/

open Lean Belay.Sqlite.Model.Conformance

/-- Report transport problems independently of semantic agreement. -/
def harnessError (message : String) : Json :=
  Json.mkObj [("verdict", toJson "HARNESS_ERROR"), ("error", toJson message)]

/-- The width at which the case term is rendered: wide enough that the term stays on one
line. A wrapped term can break Lean's column rule for structure instances, because the
`Repr` of `some` does not indent the lines that follow it. -/
def caseTermWidth : Nat := 1000000000

/-- Both verdict and optional proof input originate in one decoded structural case. -/
def evaluateLine (line : String) (emitLean : Bool) : Json :=
  match Json.parse line >>= decodeCase with
  | .error message => harnessError message
  | .ok c =>
    let verdict := classifyCase c
    let (name, position) := match verdict with
      | .agree => ("AGREE", none)
      | .disagree position => ("DISAGREE", position)
      | .modelUnsupported => ("MODEL_UNSUPPORTED", none)
    Json.mkObj ([("verdict", toJson name), ("position", toJson position)] ++
      if emitLean then [("caseLean", toJson ((repr c).pretty caseTermWidth)), ("decoded", toJson c)] else [])

/-- One prediction, or an error object that the judge counts as a harness error. -/
def predictLine (line : String) : Json :=
  match Json.parse line >>= fromJson? with
  | .error message => Json.mkObj [("error", toJson message)]
  | .ok (input : PredictInput) => predict input

/-- Each input line produces exactly one result; malformed lines do not poison the stream. -/
def main (args : List String) : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  unless args == [] || args == ["--emit-lean"] || args == ["--predict"] do
    (← IO.getStderr).putStrLn "usage: conformance-runner [--emit-lean | --predict]"
    return 2
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := if args == ["--predict"] then predictLine line else evaluateLine line (args == ["--emit-lean"])
    output.putStrLn result.compress
  return 0
