import Belay
import Belay.Sqlite.Model.Codec.SyntaxJson

/-! The equality of candidate A, the Lean port of the translation (ADR 0017, S1, prototype 2),
with the Python translation over the texts of {lit}`build/surface-s1/texts.jsonl` (from
{lit}`texts.py`): each text is parsed with its grammar, translated in this process, and its
result compared with the Python translation's result, the statements with the range of each
node or the refusal. Each statement also decodes to the model's {lit}`Syntax.Statement`. The
first differences go to {lit}`build/surface-s1/differences-a.jsonl`. Run with the surface's
plugin, as {lit}`README.md` says. -/

open Belay.Sqlite Belay.Sqlite.Translation Lean

/-- The number of differences written to the file: enough to see their kinds, and a small file. -/
def writtenDifferences : Nat := 50

#eval show IO Unit from do
  let lines ← IO.FS.lines "build/surface-s1/texts.jsonl"
  let output ← IO.FS.Handle.mk "build/surface-s1/differences-a.jsonl" .write
  let mut (texts, equal, refused, statements, undecoded, nanos) := (0, 0, 0, 0, 0, 0)
  for line in lines do
    let json ← IO.ofExcept (Json.parse line)
    let some python := (json.getObjVal? "python").toOption | continue
    let grammar ← IO.ofExcept (json.getObjValAs? String "grammar")
    let sql ← IO.ofExcept (json.getObjValAs? String "sql")
    let start ← IO.monoNanosNow
    let result ← translationJson grammar sql
    nanos := nanos + ((← IO.monoNanosNow) - start)
    texts := texts + 1
    if result.compress == python.compress then equal := equal + 1
    else if texts - equal ≤ writtenDifferences then
      output.putStrLn (Json.mkObj [("case", json.getObjValD "case"), ("role", json.getObjValD "role"),
        ("lean", result), ("python", python)]).compress
    if let .ok items := result.getObjValAs? (Array Json) "statements" then
      for item in items do
        statements := statements + 1
        if let .error _ := (fromJson? (item.getObjValD "value") : Except String Model.Syntax.Statement) then
          undecoded := undecoded + 1
    else refused := refused + 1
  IO.println s!"texts {texts} equal {equal} refused {refused} statements {statements} undecoded {undecoded} parse and translation ms {nanos / 1000000}"
