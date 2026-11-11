import Belay.Sqlite.Model.Programs.StatementRunLaws.AdmittedAtomsCounterExamples
import Belay.Sqlite.Model.Schema.Rows.AdmittedAtomsNestedExamples

set_option doc.verso true

/-! A statement with trigger programs whose nested write is not described (ADR 0022, slice 4, part 2;
finding 16 of the status file and the owner decision M), checked by the kernel. An INSERT runs an AFTER
INSERT trigger whose UPDATE would write the rowid {lit}`2 ^ 70`, which is out of range, into a second
table, and an AFTER UPDATE trigger of that table would stop the write with {lit}`RAISE(FAIL)`. Before the
decision the run was ready and the database that the error {lit}`constraintFail` keeps had the rowid out of
range. Now the row engine tests every row that it writes ({lit}`LiteralData.rowAdmitted`), so the run is not
ready and ends as {lit}`unmodeled` with the input database. -/

namespace Belay.Sqlite.Model.AdmittedAtomsNestedExamples

open Belay.Sqlite.Model

example : (runStatement 0 {} [] nestedInsert twoTables).effect = .error (.unmodeled, twoTables) := by rfl
-- The effect satisfies every property of databases, because it is neither a success nor a `constraintFail`.
example (property : Database → Prop) : (runStatement 0 {} [] nestedInsert twoTables).effect.Satisfies property := by
  intro database kept
  have effect : (runStatement 0 {} [] nestedInsert twoTables).effect = .error (.unmodeled, twoTables) := by rfl
  rw [effect] at kept
  rcases kept with same | same <;> cases same

end Belay.Sqlite.Model.AdmittedAtomsNestedExamples
