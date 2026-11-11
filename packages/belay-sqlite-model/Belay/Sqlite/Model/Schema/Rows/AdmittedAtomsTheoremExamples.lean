import Belay.Sqlite.Model.Schema.Rows.AdmittedAtomsEngineExamples
import Belay.Sqlite.Model.Schema.Rows.AdmittedRowsOnly

set_option doc.verso true

namespace Belay.Sqlite.Model.AdmittedAtomsTheoremExamples

open Belay.Sqlite.Model AdmittedAtomsExamples AdmittedAtomsEngineExamples Resolution.Examples

/-- Write rules with the foreign key check on. -/
def someRules : Resolved.WriteRules := { depth := 1, keys := true }

-- A write that stores the rows of the table at its target is {name}`Database.RowsOnlyAt` the database.
example : emptyDatabase.RowsOnlyAt 0 (emptyDatabase.setRows 0 []) := .setRows (table := { shape := twoColumns, rows := [] }) rfl []
-- A write that fails keeps the database.
example : emptyDatabase.RowsOnlyAt 0 emptyDatabase := .inl rfl
-- A change of the rows at the index, which holds no table, is not allowed: the catalog position 1 is an index.
example : ¬ emptyDatabase.RowsOnlyAt 1 (emptyDatabase.setRows 1 [{ rowid := 1, values := [] }]) := by
  rintro (same | ⟨table, _, found, _⟩)
  · exact absurd (congrArg Database.rows same) (by decide +kernel)
  · have none : emptyDatabase.table 1 = none := by decide +kernel
    rw [none] at found
    cases found

-- DROP of the table alone leaves an index without its table: its catalog is not valid, so the
-- condition of the theorem fails, and so does the conclusion (the statement succeeds).
example : ¬ ((.drop [0] none : Resolved.Statement).applyCatalog emptyDatabase.catalog).Valid defaults.limits := by
  decide +kernel

end Belay.Sqlite.Model.AdmittedAtomsTheoremExamples
