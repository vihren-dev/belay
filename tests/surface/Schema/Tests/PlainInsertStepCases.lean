import InsertSelectExamples
import Belay.Sqlite.Model.Programs.Scripts.PlainInsertRule

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

/-- The literal insert writes both rows once, reports two changes, and leaves the last rowid at 2. The proof
rewrites with the simp set {lit}`step_rule`, so it checks that the kind rule {name}`runScriptStep_plainInsert_eq` is
in the set. Proof sketch: the kind rule gives the step; the clock, the counters and the table select its success
case, with {name}`insertReady_of_fits` and {name}`insertOutcome_of_fits` for the rows that fit; then evaluate the
resulting connection. -/
theorem two_rows : ∃ next, stepOf begin insertTwo = .continued (.done 2) next [] ∧
    (next.state.database.table 1).map (fun t => t.rows.map (·.values)) = some selected ∧
    next.state.counters.lastInsertRowid = some 2 := by
  have resolves : resolvesTo begin insertTwo (.insert 1 literalCells [] [] none) = true := by decide +kernel
  obtain ⟨after, found⟩ := resolvesTo_sound resolves
  have timed : statementClock environment.clock 0 (.insert 1 literalCells [] [] none) = some 0 := by decide +kernel
  have known : begin.state.counters.firstUnknown (Resolved.Statement.insert 1 literalCells [] [] none).counterReads =
      none := by decide +kernel
  simp (disch := assumption) only [stepOf, step_rule]
  simp only [timed, known, dst_present]
  simp only [literalCells, Resolved.rowsAt_values, cellsReady_values, insertReady_of_fits two_fit,
    insertOutcome_of_fits two_fit, Resolved.subqueriesPlain, List.all_nil, Bool.and_self, ite_true]
  exact ⟨_, rfl, by decide +kernel, by decide +kernel⟩

/-- Neither new id occurs in the old table, but their duplicate still fails in the same INSERT. -/
example : outputOf begin (statementOf (sql r"INSERT INTO dst VALUES (1,'a'), (1,'b')")) = some (.error 19) := by
  decide +kernel

#print axioms fits_with_unique_name
#print axioms two_rows
end PlainInsertStepCases
