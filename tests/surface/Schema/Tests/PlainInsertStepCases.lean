import InsertSelectExamples
import Belay.Sqlite.Model.Programs.Scripts.PlainInsertStep

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace PlainInsertStepCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SchemaStepLaws InsertSelectExamples

/-- Two distinct literals for the empty destination of the copy example. -/
def insertTwo : Syntax.Statement := statementOf (sql r"INSERT INTO dst VALUES (1,'a'), (2,'b')")

/-- The two rows as known cells after resolution. -/
def literalCells : List (List Resolved.Cell) := selected.map (·.map Resolved.Cell.value)

/-- The literal insert writes both rows once, reports two changes, and leaves the last rowid at 2.
Proof sketch: instantiate the library step law, then evaluate its resulting connection. -/
theorem two_rows : ∃ next, stepOf begin insertTwo = .continued (.done 2) next [] ∧
    (next.state.database.table 1).map (fun t => t.rows.map (·.values)) = some selected ∧
    next.state.counters.lastInsertRowid = some 2 := by
  have resolves : resolvesTo begin insertTwo (.insert 1 literalCells [] [] none) = true := by decide +kernel
  obtain ⟨after, found⟩ := resolvesTo_sound resolves
  have step := runScriptStep_insert_ok (clock := environment.clock) (index := 0) (parameters := [])
    (value := 0) (table := dstTable) found (by decide +kernel) (by decide +kernel) dst_present (by decide +kernel)
    (by decide +kernel) (by exact written_fit)
  exact ⟨_, step, by decide +kernel, by decide +kernel⟩

/-- Neither new id occurs in the old table, but their duplicate still fails in the same INSERT. -/
example : outputOf begin (statementOf (sql r"INSERT INTO dst VALUES (1,'a'), (1,'b')")) = some (.error 19) := by
  decide +kernel

#print axioms two_rows
end PlainInsertStepCases
