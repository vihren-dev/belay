import Belay.Sqlite.Model.AdmittedAtomsCounterExamples

set_option doc.verso true

/-! A counterexample to "rowids in range" for a statement with trigger programs (ADR 0022, slice 4,
part 2; finding 16 of the status file), checked by the kernel. An INSERT runs an AFTER INSERT trigger
whose UPDATE writes a rowid out of range into a second table, and an AFTER UPDATE trigger of that
table stops the write with {lit}`RAISE(FAIL)`. The run is ready, and the database that the error
{lit}`constraintFail` keeps has the rowid out of range. So the theorems of the four atoms that need the
support check ask for a statement without rules. -/

namespace Belay.Sqlite.Model.AdmittedAtomsNestedExamples

open Belay.Sqlite.Model AdmittedAtomsCounterExamples

/-- The table {lit}`u(id INTEGER PRIMARY KEY)` with the row {lit}`(1)` at the rowid 1. -/
def keyedTable : Table :=
  { shape := { columns := [{ columnA with name := Identifier.ofString "id" }], primaryKey := [0], rowidAlias := some 0 },
    rows := [{ rowid := 1, values := [.integer 1] }] }

/-- The database with {name}`emptyTable` at position 0 and {name}`keyedTable` at position 1. -/
def twoTables : Database :=
  .ofTables [(Identifier.ofString "s", emptyTable), (Identifier.ofString "u", keyedTable)]

/-- The program of an AFTER INSERT trigger on the table at position 0: an UPDATE of the table at
position 1 that sets the alias to the integer {lit}`2 ^ 70`. A resolved program can hold this integer,
although the resolver does not make it from SQL text. -/
def updateProgram : Resolved.Program :=
  { trigger := 2, table := 0, time := .after, event := .insert, width := 1, condition := none,
    body := [.update 1 [(0, .literal (.integer (2 ^ 70)))] none []] }

/-- The program of an AFTER UPDATE trigger on the table at position 1: {lit}`RAISE(FAIL)`. -/
def raiseProgram : Resolved.Program :=
  { trigger := 3, table := 1, time := .after, event := .update none, width := 1, condition := none,
    body := [.raise none [] (some .fail)] }

/-- The INSERT of one row into the table at position 0 with the two programs. -/
def nestedInsert : Resolved.Statement :=
  .insert 0 [[.value (.integer 1)]] [] [] (some { depth := 3, keys := false, programs := [updateProgram, raiseProgram] })

/-- The database after {name}`nestedInsert`: the row of the INSERT is kept, and the row of the UPDATE has
the rowid {lit}`2 ^ 70`. -/
def nestedAfter : Database :=
  { twoTables with rows := [[{ rowid := 1, values := [.integer 1] }], [{ rowid := 2 ^ 70, values := [.integer (2 ^ 70)] }]] }

-- Finding 16: the nested UPDATE writes the rowid 2 ^ 70, and the FAIL of the nested trigger stops the
-- write with the error `constraintFail`, which keeps the database. The run is ready, so the rowid
-- is out of range in a database that the theorem would keep. The theorems of "rowids in range" ask for
-- a statement without rules ({name}`Resolved.Statement.WithoutRules`).
example : twoTables.RowidsInRange := by
  intro position table found row member
  rcases position with _ | _ | position
  · have same : table = emptyTable := Option.some.inj (found.symm.trans rfl)
    subst same
    simp [emptyTable] at member
  · have same : table = keyedTable := Option.some.inj (found.symm.trans rfl)
    subst same
    simp only [keyedTable, List.mem_singleton] at member
    subst member
    exact ⟨by decide, by decide⟩
  · have none : twoTables.table (position + 2) = none := by
      simp [twoTables, Database.ofTables, Database.table, Catalog.tableAt]
    rw [none] at found
    cases found
example : ¬ nestedInsert.WithoutRules := nofun
example : (runStatement 0 {} [] nestedInsert twoTables).ready = true := by decide +kernel
example : (runStatement 0 {} [] nestedInsert twoTables).effect = .error (.constraintFail, nestedAfter) := by rfl
example : ¬ (runStatement 0 {} [] nestedInsert twoTables).effect.Satisfies Database.RowidsInRange := by
  intro satisfies
  have inRange := satisfies nestedAfter (.inr (by rfl))
  have row := inRange 1 { keyedTable with rows := [{ rowid := 2 ^ 70, values := [.integer (2 ^ 70)] }] } rfl
    { rowid := 2 ^ 70, values := [.integer (2 ^ 70)] } (by decide +kernel)
  exact absurd row.2 (by decide)

end Belay.Sqlite.Model.AdmittedAtomsNestedExamples
