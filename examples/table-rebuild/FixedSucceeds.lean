import TableRebuild
import RebuildSucceeds -- the proof of `fixed_succeeds`, in the folder `Proof`

/-! The success of the fixed migration of `TableRebuild.lean`. A migration that fails keeps every
read, so a claim about a read goes with a claim of success. The fixed migration does not succeed on
every database of `shop`: the STRICT copy refuses a customer whose email is a blob. -/

open Belay.Sqlite

-- Answers `false`, with a customer whose email is a blob.
#sql_check fixedMigration succeeds on shop

/-- For every database with the catalog of `shop` whose customers all fit the STRICT types of the
new table (`RebuildGuide.StrictRows`), and every complete environment: `fixedMigration` runs without
an error, on the actual run and on every branch. Where a customer does not fit, for example with a
blob email, the claim requires nothing. Proof sketch: `RebuildGuide.makeStrict_succeeds` in
`Proof/RebuildSucceeds.lean`, with `shop_catalog`. -/
theorem fixed_succeeds :
    Succeeds fixedMigration (fun db => db.HasCatalog shop ∧ RebuildGuide.StrictRows db) := by
  intro db ⟨onShop, fits⟩
  exact RebuildGuide.makeStrict_succeeds db ⟨onShop.trans shop_catalog, fits⟩

#print axioms fixed_succeeds
