import Belay

/-! The parse time of the SQL texts of the frozen corpora in the Lean process (ADR 0017, S1,
prototype 1): each text of {lit}`build/surface-s1/sql.jsonl` (from {lit}`texts.py`), parsed with
its grammar through the surface's binding and read into a tree, while this file elaborates.
Run with the surface's plugin, as {lit}`README.md` says. -/

open Belay.Sqlite Lean

#eval show IO Unit from do
  let lines ← IO.FS.lines "build/surface-s1/sql.jsonl"
  let mut times : Array Nat := #[]
  let mut parsed := 0
  for line in lines do
    let json ← IO.ofExcept (Json.parse line)
    let grammar ← IO.ofExcept (json.getObjValAs? String "grammar")
    let sql := (← IO.ofExcept (json.getObjValAs? String "sql")).toUTF8
    let start ← IO.monoNanosNow
    let result ← IO.ofExcept (decodeParse grammar sql.size (← ParserLibrary.parse grammar sql))
    times := times.push ((← IO.monoNanosNow) - start)
    if let .parsed .. := result then parsed := parsed + 1
  let sorted := times.qsort (· < ·)
  IO.println s!"texts {times.size} parsed {parsed} total ms {times.foldl (· + ·) 0 / 1000000} median us {sorted[sorted.size / 2]! / 1000} max ms {sorted.back! / 1000000}"
