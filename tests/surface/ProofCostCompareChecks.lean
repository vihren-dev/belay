import Belay.Sqlite.ProofCostCompare
import Belay.Sqlite.ProofCostArguments

/-! Checks of the pure parts of the proof-cost report: the comparison rule at its boundary, the
classification of baseline entries, the order of the report, and the command line. -/

open Belay.Sqlite

/-- A completed record of a stable theorem. -/
def entry (module declaration : String) (count : Nat) (status : ProofCostStatus := .completed)
    (identity : ProofCostIdentity := .stable) (compiler : String := "4.34.1") : ProofCostRecord :=
  { module, declaration, kind := .thm, identity, status,
    heartbeats := if status == .completed then some count else none,
    compiler, scheme := "proof-body-v1-async", sourceHash := 7 }

/-- A library with the given records and unmeasured theorem names of module {lit}`M`. -/
def library (records : Array ProofCostRecord) (unmeasured : Array String := #[]) : LibraryCosts :=
  { name := "L", records, unmeasured := unmeasured.map ({ module := "M", declaration := · }), stale := #[] }

def baseline : LibraryCosts := library #[entry "M" "a" 10000, entry "M" "b" 5000]
def compare' (allowance : Nat) (now : LibraryCosts) : LibraryComparison :=
  compareLibrary allowance (some baseline) now

-- the boundary: equal to baseline plus allowance passes, one internal unit more fails
#guard (compare' 2500 (library #[entry "M" "a" 12500, entry "M" "b" 5000])).growth.isEmpty
#guard (compare' 2500 (library #[entry "M" "a" 12501, entry "M" "b" 5000])).growth.size == 1
#guard (compare' 0 (library #[entry "M" "a" 10000, entry "M" "b" 4000])).growth.isEmpty
-- a smaller count is not growth
-- another compiler is incompatible, and not growth
#guard (compare' 0 (library #[entry "M" "a" 99999 (compiler := "5.0.0"), entry "M" "b" 5000])).incompatible.size == 1
#guard (compare' 0 (library #[entry "M" "a" 99999 (compiler := "5.0.0"), entry "M" "b" 5000])).growth.isEmpty
-- a baseline proof with no completed count now is listed with its cause, never as zero
#guard (compare' 0 (library #[entry "M" "b" 5000])).missing.map (·.2 == .absent) == #[true]
#guard (compare' 0 (library #[entry "M" "b" 5000] #["a"])).missing.map (·.2 == .unmeasured) == #[true]
#guard (compare' 0 (library #[entry "M" "a" 0 .failed, entry "M" "b" 5000])).missing.map (·.2 == .failed) == #[true]
#guard (compare' 0 (library #[entry "M" "a" 0 .precisionUnavailable, entry "M" "b" 5000])).missing.map (·.2 == .precisionUnavailable) == #[true]
-- new stable proofs are added; unstable names are not compared
#guard (compare' 0 (library #[entry "M" "a" 10000, entry "M" "b" 5000, entry "M" "c" 1])).added.size == 1
#guard (compare' 0 (library #[entry "M" "a" 10000, entry "M" "b" 5000, entry "M" "p" 1 (identity := .privateName)])).added.isEmpty
-- exit codes
#guard comparisonExit #[compare' 0 baseline] == 0
#guard comparisonExit #[compare' 0 (library #[entry "M" "a" 10001, entry "M" "b" 5000])] == 1
#guard comparisonExit #[compare' 0 (library #[entry "M" "b" 5000])] == 1
#guard comparisonExit #[compare' 0 (library #[entry "M" "a" 99999 (compiler := "5.0.0"), entry "M" "b" 5000])] == 2
#guard comparisonExit #[compare' 0 (library #[entry "M" "a" 10000, entry "M" "b" 5000, entry "M" "c" 1])] == 0
-- the order of a report: by module, then declaration, and a theorem without a completed count is unmeasured
#guard (LibraryCosts.ofModules "L" #[
    { module := "Z", records := #[entry "Z" "x" 1], theorems := #["x"], stale := false },
    { module := "A", records := #[entry "A" "b" 1, entry "A" "a" 2], theorems := #["a", "b", "c", "d"], stale := true }]
  ).unmeasured.map (·.declaration) == #["c", "d"]
#guard (LibraryCosts.ofModules "L" #[
    { module := "Z", records := #[entry "Z" "x" 1], theorems := #["x"], stale := false },
    { module := "A", records := #[entry "A" "b" 1, entry "A" "a" 2], theorems := #[], stale := true }]
  ).records.map (·.declaration) == #["a", "b", "x"]
-- the baseline is the report
#guard (costsOfJson (costsJson #[baseline])).toOption.map (·.map (·.records.size)) == some #[2]
-- the command line
#guard (parseArguments ["--costs", "--baseline", "b.json", "--allowance", "2.5"]).isOk
#guard (parseArguments []).isOk
#guard !(parseArguments ["--costs", "--baseline", "b.json"]).isOk
#guard !(parseArguments ["--costs", "--allowance", "1"]).isOk
#guard !(parseArguments ["--costs", "--baseline", "b.json", "--allowance", "0.0001"]).isOk
#guard !(parseArguments ["--costs", "--baseline", "b.json", "--allowance", "-1"]).isOk
#guard !(parseArguments ["--json"]).isOk
#guard !(parseArguments ["--costs", "--json", "--baseline", "b.json", "--allowance", "1"]).isOk
#eval IO.println "CHECKS \"passed\""
