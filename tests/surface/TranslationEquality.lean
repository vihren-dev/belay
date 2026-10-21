import Belay
import Belay.Sqlite.Model.Codec.SyntaxJson

/-! The fixture of {lit}`tests/surface_translation_test.py` and the measurement of candidate A
(ADR 0017, S1, prototype 2): each line of the file that {lit}`BELAY_TRANSLATION_TEXTS` names has a
grammar, an SQL text and the Python translation's result. This file translates each text with the
Lean port ({lit}`Belay.Sqlite.Translation`) and compares the results: each statement's value with
the Python statement decoded by the model's codec, its ranges with the Python ranges, and a refusal
with the Python diagnostic. It prints the counts and the translation time, then each text whose
results differ, and fails when one differs. -/

open Belay.Sqlite Belay.Sqlite.Model Belay.Sqlite.Translation Lean

/-- The number of differences printed: enough to see their kinds in the test's output. -/
def printedDifferences : Nat := 5

/-- The ranges of a located value of the Python translation: its start, end and children. -/
partial def pythonSpan (json : Json) : Except String Span := do
  let children ← json.getObjValAs? (Array Json) "children"
  return { start := ← json.getObjValAs? Nat "start", stop := ← json.getObjValAs? Nat "end",
           parts := ← children.mapM pythonSpan }

/-- Whether a statement of the Lean port equals a located statement of the Python translation:
the Python value decodes to the same statement, and the ranges are the same. -/
def sameStatement (lean : Located Syntax.Statement) (python : Json) : Bool :=
  match (fromJson? (python.getObjValD "value") : Except String Syntax.Statement), pythonSpan python with
  | .ok value, .ok span => value == lean.value && span == lean.span
  | _, _ => false

/-- Whether the Lean port's result equals the Python translation's result for one text: the same
statements, or the same refusal. -/
def sameResult (lean : Except Refusal (Array (Located Syntax.Statement))) (python : Json) : Bool :=
  match lean, python.getObjValAs? (Array Json) "statements" with
  | .ok items, .ok expected => items.size == expected.size && (items.zip expected).all fun (item, other) =>
    sameStatement item other
  | .error refusal, .error _ => (refusal.toJson "measured.sql").compress == (python.getObjValD "refusal").compress
  | _, _ => false

/-- A range tree as JSON, for the report of a difference. -/
partial def spanJson (span : Span) : Json :=
  Json.mkObj [("start", span.start), ("end", span.stop), ("children", .arr (span.parts.map spanJson))]

/-- The Lean port's result as JSON, for the report of a difference: each statement in the model's
transport with its ranges, or the refusal. -/
def resultJson : Except Refusal (Array (Located Syntax.Statement)) → Json
  | .ok items => Json.mkObj [("statements", .arr (items.map fun item =>
      Json.mkObj [("value", toJson item.value), ("span", spanJson item.span)]))]
  | .error refusal => Json.mkObj [("refusal", refusal.toJson "measured.sql")]

#eval show IO Unit from do
  let some path ← IO.getEnv "BELAY_TRANSLATION_TEXTS"
    | throw <| IO.userError "BELAY_TRANSLATION_TEXTS is not set; set it to the texts file of the test"
  let mut (texts, refused, statements, nanos, different) := (0, 0, 0, 0, #[])
  for line in ← IO.FS.lines path do
    let json ← IO.ofExcept (Json.parse line)
    let grammar ← IO.ofExcept (json.getObjValAs? String "grammar")
    let sql ← IO.ofExcept (json.getObjValAs? String "sql")
    let start ← IO.monoNanosNow
    let lean ← translate grammar sql
    nanos := nanos + ((← IO.monoNanosNow) - start)
    texts := texts + 1
    match lean with
    | .ok items => statements := statements + items.size
    | .error _ => refused := refused + 1
    unless sameResult lean (json.getObjValD "python") do
      different := different.push (Json.mkObj [("sql", sql), ("lean", resultJson lean), ("python", json.getObjValD "python")])
  IO.println s!"texts {texts} different {different.size} refused {refused} statements {statements} parse and translation ms {nanos / 1000000}"
  for item in different.extract 0 printedDifferences do IO.println item.compress
  unless different.isEmpty do throw <| IO.userError s!"{different.size} of {texts} translations differ"
