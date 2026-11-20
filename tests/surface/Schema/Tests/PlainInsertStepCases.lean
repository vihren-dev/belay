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

/-- The rows supplied with explicit integer primary keys. -/
def incoming : List Row := [⟨1, [.integer 1, .text [97]]⟩, ⟨2, [.integer 2, .text [98]]⟩]

/-- The two explicit ids are distinct and fresh in the target. Validity supplies the
constraints on its stored rows. Proof sketch: apply the alias law and check the new rows. -/
theorem two_fit : InsertFits (begin.state.database.keys 1 dstTable) dstTable selected := by
  apply InsertFits.of_valid_alias warehouse.valid dst_present (position := 0) (by decide +kernel)
    (by decide +kernel) (rows := incoming)
  · intro key member
    refine ⟨.binary, ?_⟩
    revert key
    decide +kernel
  · decide +kernel
  · exact (Table.rowsWide_iff _).1 (by decide +kernel)
  · exact (Table.rowsStored_iff _).1 (by decide +kernel)
  · exact (Table.notNullRows_iff _).1 (by decide +kernel)
  · exact (Table.typedRows_iff _).1 (by decide +kernel)
  · exact (Table.checkedRows_iff _).1 (by decide +kernel)
  · exact (Table.rowidsInRange_iff _).1 (by decide +kernel)
  · exact (Table.rowidsDistinct_iff _).1 (by decide +kernel)
  · decide +kernel

/-- A nonempty target has a separate UNIQUE name. SQLite allocates an id for the
first NULL alias. A second row supplies its own id and a NULL name.
Proof sketch: check the batch constraints and its freshness against the stored row. -/
theorem fits_with_unique_name :
    let table := (begin.state.database.table 3).get (by decide +kernel)
    InsertFits (begin.state.database.keys 3 table) table [[.null, .text [98]], [.integer 12, .null]] := by
  intro table
  apply InsertFits.of_valid warehouse.valid (target := 3) (table := table) (Option.some_get _).symm
  · decide +kernel
  · decide +kernel
  · exact (Table.notNullRows_iff _).1 (by decide +kernel)
  · exact (Table.typedRows_iff _).1 (by decide +kernel)
  · exact (Table.checkedRows_iff _).1 (by decide +kernel)
  · exact (Table.rowidsInRange_iff _).1 (by decide +kernel)
  · exact (Table.rowidsDistinct_iff _).1 (by decide +kernel)
  · decide +kernel
  · exact (Table.keysUnique_iff _ _).1 (by decide +kernel)
  · decide +kernel

/-- The literal insert writes both rows once, reports two changes, and leaves the last rowid at 2.
Proof sketch: instantiate the library step law, then evaluate its resulting connection. -/
theorem two_rows : ∃ next, stepOf begin insertTwo = .continued (.done 2) next [] ∧
    (next.state.database.table 1).map (fun t => t.rows.map (·.values)) = some selected ∧
    next.state.counters.lastInsertRowid = some 2 := by
  have resolves : resolvesTo begin insertTwo (.insert 1 literalCells [] [] none) = true := by decide +kernel
  obtain ⟨after, found⟩ := resolvesTo_sound resolves
  have step := runScriptStep_insert_ok (clock := environment.clock) (index := 0) (parameters := [])
    (value := 0) (table := dstTable) found (by decide +kernel) (by decide +kernel) dst_present (by decide +kernel)
    (by decide +kernel) (by exact two_fit)
  exact ⟨_, step, by decide +kernel, by decide +kernel⟩

/-- Neither new id occurs in the old table, but their duplicate still fails in the same INSERT. -/
example : outputOf begin (statementOf (sql r"INSERT INTO dst VALUES (1,'a'), (1,'b')")) = some (.error 19) := by
  decide +kernel

#print axioms fits_with_unique_name
#print axioms two_rows
end PlainInsertStepCases
