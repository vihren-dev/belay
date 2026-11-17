import RebuildKeepsInvariant

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-! The statement that copies the customers and its source and target definitions.
The rebuild's resolution path gives both definitions immediately before the INSERT. -/
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- The name of the table of the customers. -/
def customersName : Identifier := name! "customers"

/-- The query of the copy: the three columns of the table at position 0, the old customers, in order. -/
def copyQuery : Resolved.Query :=
  Resolved.Query.simple [Resolved.QuerySource.first 0] none ((List.range 3).map fun position => .scalar (.column position))
    ["id", "name", "email"]

/-- The resolved copy: the table at position 2, the new customers, takes the three cells of the query in order. -/
def copyStatement : Resolved.Statement :=
  .insertSelect 2 ((List.range 3).map .source) copyQuery [] [] none [] none

/-- The fourth statement of the rebuild resolves to {name}`copyStatement` on the resolution state that {name}`schemaAt`
computes after the first three statements. Proof sketch: evaluation. -/
theorem copy_resolves : ∃ after, resolveStatement runContext (schemaAt 3) makeStrict.statements[3].1 =
    .ok (copyStatement, after) := ⟨_, by with_unfolding_all rfl⟩

/-- The resolved definition at the source of the copy, before the fourth statement. -/
def sourceShape : CatalogTable := ((schemaAt 3).catalog.tableAt 0).getD { columns := [] }

/-- The definition of the new customers, as the model builds it for the CREATE TABLE of the rebuild: the table at
position 2 of the catalog that the resolver computes after the first three statements. The premise of the success claim
asks that every old customer fits its STRICT types ({name}`LiteralData.typesFit`). The table without columns is not
reached; it only completes the lookup. -/
def strictShape : CatalogTable := ((schemaAt 3).catalog.tableAt 2).getD { columns := [] }

end RebuildGuide
