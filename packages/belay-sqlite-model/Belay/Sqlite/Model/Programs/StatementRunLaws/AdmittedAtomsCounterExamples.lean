import Belay.Sqlite.Model.Programs.Scripts.AdmittedAtomsTheoremExamples
import Belay.Sqlite.Model.Schema.Rows.AdmittedAtomsCounterExamples

set_option doc.verso true

/-! Counterexamples to the statement theorems of the Admitted atoms (ADR 0022, slice 4, part 2), each
checked by the kernel. Each one runs a plain INSERT on a database that satisfies the atom, and the
atom fails after the statement. They show what the hypotheses of the theorems keep out:
* an INSERT after the largest rowid (the run is not ready), against "rowids in range";
* a cell that is not in stored form, against "rows stored";
* a row with fewer cells than columns, against "rows wide";
* a rowid alias column of TEXT affinity (the run is not ready), against "rows stored";
* a rowid alias column that is generated (the run is ready; the catalog is not valid), against
  "rows aliased". -/

namespace Belay.Sqlite.Model.AdmittedAtomsCounterExamples

open Belay.Sqlite.Model

/-- For every effect, database after and atom: if the effect is a success with the database after, and
the database after does not satisfy the atom, the effect does not satisfy it ({name}`Effect.Satisfies`).
Proof sketch: a success is one of the databases that the effect keeps. -/
theorem not_satisfies_of_ok {effect : Effect} {after : Database} {atom : Database → Prop}
    (ok : effect = .ok after) (broken : ¬ atom after) : ¬ effect.Satisfies atom :=
  fun satisfies => broken (satisfies after (.inl ok))

example : ¬ (runStatement 0 {} [] (insertCells [.value (.integer 2)]) (oneTable largestRowidTable)).effect.Satisfies
    Database.RowidsInRange := by
  refine not_satisfies_of_ok (after := (oneTable largestRowidTable).setRows 0
    [{ rowid := 2 ^ 63 - 1, values := [.integer 1] }, { rowid := 2 ^ 63, values := [.integer 2] }]) (by rfl) ?_
  intro inRange
  have row := inRange 0 { emptyTable with rows := [{ rowid := 2 ^ 63 - 1, values := [.integer 1] },
    { rowid := 2 ^ 63, values := [.integer 2] }] } rfl { rowid := 2 ^ 63, values := [.integer 2] } (by decide +kernel)
  exact absurd row.2 (by decide)

example : ¬ (runStatement 0 {} [] (insertCells [.value (.text [53])]) (oneTable emptyTable)).effect.Satisfies
    Database.RowsStored := by
  refine not_satisfies_of_ok (after := (oneTable emptyTable).setRows 0 [{ rowid := 1, values := [.text [53]] }])
    (by rfl) ?_
  intro stored
  have cell := stored 0 { emptyTable with rows := [{ rowid := 1, values := [.text [53]] }] } rfl
    { rowid := 1, values := [.text [53]] } (by decide +kernel) 0 columnA (.text [53]) rfl rfl
  exact absurd cell (by decide +kernel)

example : ¬ (runStatement 0 {} [] (insertCells []) (oneTable emptyTable)).effect.Satisfies Database.RowsWide := by
  refine not_satisfies_of_ok (after := (oneTable emptyTable).setRows 0 [{ rowid := 1, values := [] }]) (by rfl) ?_
  intro wide
  have width := wide 0 { emptyTable with rows := [{ rowid := 1, values := [] }] } rfl { rowid := 1, values := [] }
    (by decide +kernel)
  exact absurd width (by decide)

example : ¬ (runStatement 0 {} [] (insertCells [.value .null]) (oneTable textAliasTable)).effect.Satisfies
    Database.RowsStored := by
  refine not_satisfies_of_ok (after := (oneTable textAliasTable).setRows 0 [{ rowid := 1, values := [.integer 1] }])
    (by rfl) ?_
  intro stored
  have cell := stored 0 { textAliasTable with rows := [{ rowid := 1, values := [.integer 1] }] } rfl
    { rowid := 1, values := [.integer 1] } (by decide +kernel) 0 columnText (.integer 1) rfl rfl
  exact absurd cell (by decide +kernel)

example : ¬ (runStatement 0 {} [] (insertCells [.value .null]) (oneTable generatedAliasTable)).effect.Satisfies
    Database.RowsAliased := by
  refine not_satisfies_of_ok (after := (oneTable generatedAliasTable).setRows 0
    [{ rowid := 1, values := [.null] }]) (by rfl) ?_
  intro aliased
  have cell := aliased 0 { generatedAliasTable with rows := [{ rowid := 1, values := [.null] }] } rfl
    { rowid := 1, values := [.null] } (by decide +kernel) 0 rfl
  exact absurd cell (by decide +kernel)

end Belay.Sqlite.Model.AdmittedAtomsCounterExamples
