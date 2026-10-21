import Belay

/-! The fixture of {lit}`tests/surface_translation_test.py`: each line of the file that
{lit}`BELAY_TRANSLATION_TEXTS` names has a grammar, an SQL text and the Python translation's
result; this file translates each text with the Lean port ({lit}`Belay.Sqlite.Translation`)
and compares the results. It prints the counts, then each text whose results differ, and fails
when one differs. -/

open Belay.Sqlite.Translation Lean

/-- The number of differences printed: enough to see their kinds in the test's output. -/
def printedDifferences : Nat := 5

#eval show IO Unit from do
  let some path ← IO.getEnv "BELAY_TRANSLATION_TEXTS"
    | throw <| IO.userError "BELAY_TRANSLATION_TEXTS is not set; set it to the texts file of the test"
  let mut (texts, different) := (0, #[])
  for line in ← IO.FS.lines path do
    let json ← IO.ofExcept (Json.parse line)
    let grammar ← IO.ofExcept (json.getObjValAs? String "grammar")
    let sql ← IO.ofExcept (json.getObjValAs? String "sql")
    let lean ← translationJson grammar sql
    texts := texts + 1
    unless lean.compress == (json.getObjValD "python").compress do
      different := different.push (Json.mkObj [("sql", sql), ("lean", lean), ("python", json.getObjValD "python")])
  IO.println s!"texts {texts} different {different.size}"
  for item in different.extract 0 printedDifferences do IO.println item.compress
  unless different.isEmpty do throw <| IO.userError s!"{different.size} of {texts} translations differ"
