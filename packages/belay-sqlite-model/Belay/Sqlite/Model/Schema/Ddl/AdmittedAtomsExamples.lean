import Belay.Sqlite.Model.Schema.Columns.AdmittedAtomsExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.AdmittedAtomsExamples

open Belay.Sqlite.Model Resolution.Examples

/-- {lit}`t(a INTEGER, b TEXT)` and the unique index {lit}`i` on {lit}`a`. -/
def indexedCatalog : Catalog :=
  [{ name := name! "t", entry := .table twoColumns },
   { name := name! "i", entry := .index { table := 0, keys := [{ term := .column 0 }], unique := true } }]

example : indexedCatalog.Valid defaults.limits := by decide +kernel

-- A drop of the index, or of the table with its index, keeps the catalog valid; it meets the closure.
example : (indexedCatalog.drop [1]).Valid defaults.limits := by decide +kernel
example : (indexedCatalog.drop [0, 1]).Valid defaults.limits := by decide +kernel
example : indexedCatalog.DropClosed [0, 1] := by
  refine ⟨fun place object index found entry kept => ?_, fun place object trigger found entry kept => ?_⟩
  · rcases place with _ | _ | place <;> simp_all [indexedCatalog]
  · rcases place with _ | _ | place <;> simp_all [indexedCatalog]
-- A drop of the table alone keeps an index without its table: the catalog is not valid and the
-- closure fails, because the kept index at position 1 names the dropped table at position 0.
example : ¬ (indexedCatalog.drop [0]).Valid defaults.limits := by decide +kernel
example : ¬ indexedCatalog.DropClosed [0] := fun closed =>
  absurd (closed.1 1 _ _ rfl rfl (by decide)) (by decide)

-- ADD COLUMN of `c REAL` to the table keeps the catalog valid ({name}`Catalog.Valid.addColumn`).
example : (indexedCatalog.addColumn 0 { name := name! "c", declaredType := some "REAL" }).Valid defaults.limits :=
  Catalog.Valid.addColumn (by decide +kernel) rfl _ (by intro object found; cases found; decide) (by decide +kernel)

end Belay.Sqlite.Model.AdmittedAtomsExamples
