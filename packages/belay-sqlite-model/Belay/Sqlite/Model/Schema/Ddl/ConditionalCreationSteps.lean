import Belay.Sqlite.Model.Schema.Ddl.CreateIndexSuccessLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Every entry is unchanged by a drop of no positions. Proof sketch: only an index changes, and
{name}`keptBelow` of no positions keeps every position below it, so its table stays. -/
theorem CatalogEntry.afterDrop_nil (entry : CatalogEntry) : entry.afterDrop [] = entry := by
  have all (list : List Nat) : list.filter (fun _ => true) = list := List.filter_eq_self.mpr fun _ _ => rfl
  cases entry <;> simp [CatalogEntry.afterDrop, keptBelow, all]

/-- Every catalog is unchanged by a drop of no positions. Proof sketch: the filter keeps every
object, {name}`CatalogEntry.afterDrop_nil` keeps each entry, and the first components of the
indexed list are the list. -/
theorem Catalog.drop_nil (catalog : Catalog) : catalog.drop [] = catalog := by
  have all : catalog.zipIdx.filter (fun _ => true) = catalog.zipIdx := List.filter_eq_self.mpr fun _ _ => rfl
  simp only [Catalog.drop, List.contains_nil, Bool.not_false, all, CatalogEntry.afterDrop_nil]
  conv => rhs; rw [← List.zipIdx_map_fst 0 catalog]

/-- Every database is unchanged by a drop of no positions. Proof sketch: {name}`Catalog.drop_nil`
for the catalog; the filter keeps every row list, in order. -/
theorem Database.drop_nil (database : Database) : database.drop [] = database := by
  have all : database.rows.zipIdx.filter (fun _ => true) = database.rows.zipIdx :=
    List.filter_eq_self.mpr fun _ _ => rfl
  simp [Database.drop, Catalog.drop_nil, all, List.zipIdx_map_fst]

end Belay.Sqlite.Model
