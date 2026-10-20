import Belay.Sqlite.Resolution.Catalog

set_option doc.verso true

/-! The catalog change of DROP INDEX and DROP TABLE (ADR 0014, D7): the objects at some
positions leave the catalog, and the later objects move to lower positions. Resolution and
execution both use {lit}`Catalog.drop`, so they give the same catalog (ADR 0013). -/

namespace Belay.Sqlite

/-- The number of positions below the position that the drop keeps: the new position of a
kept object. For example, {lean}`keptBelow [1] 3 = 2`: dropping position 1 moves position 3
to position 2. A list with repeated positions counts each position once. -/
def keptBelow (positions : List Nat) (position : Nat) : Nat :=
  ((List.range position).filter fun below => !positions.contains below).length

/-- The entry with its catalog positions after the drop: an index names the new position
of its table ({name}`keptBelow`), and a table has no catalog positions. -/
def CatalogEntry.afterDrop (positions : List Nat) : CatalogEntry → CatalogEntry
  | .table shape => .table shape
  | .index found => .index { found with table := keptBelow positions found.table }

/-- The catalog without the objects at the positions, in catalog order, each kept object
with its catalog positions after the drop ({name}`CatalogEntry.afterDrop`). Positions past
the end change nothing, and {lean}`([] : List Nat)` keeps the catalog as it is. -/
def Catalog.drop (catalog : Catalog) (positions : List Nat) : Catalog :=
  (catalog.zipIdx.filter fun (_, position) => !positions.contains position).map fun (object, _) =>
    { object with entry := object.entry.afterDrop positions }

/-- The positions that DROP TABLE removes for the table at the position: the table, then
each index on it in catalog order. -/
def Catalog.tableObjects (catalog : Catalog) (position : Nat) : List Nat :=
  position :: catalog.zipIdx.filterMap fun (object, place) => match object.entry with
    | .index found => if found.table == position then some place else none
    | .table _ => none

/-- For every catalog and list of positions, the folded names of {name}`Catalog.drop` are a
sublist of the folded names of the catalog: a drop removes names and adds none. -/
theorem Catalog.foldedNames_drop_sublist (catalog : Catalog) (positions : List Nat) :
    (catalog.drop positions).foldedNames.Sublist catalog.foldedNames := by
  have whole : (catalog.zipIdx.map fun (pair : CatalogObject × Nat) => pair.1.name.folded) = catalog.foldedNames := by
    simp only [Catalog.foldedNames]
    conv => rhs; rw [← List.zipIdx_map_fst 0 catalog]
    rw [List.map_map]
    rfl
  rw [← whole]
  simp only [Catalog.drop, Catalog.foldedNames, List.map_map]
  exact (List.filter_sublist).map _

/-- For every catalog with unique folded names and every list of positions,
{name}`Catalog.drop` keeps the folded names unique. -/
theorem Catalog.NamesUnique.drop {catalog : Catalog} (unique : catalog.NamesUnique) (positions : List Nat) :
    (catalog.drop positions).NamesUnique :=
  (Catalog.foldedNames_drop_sublist catalog positions).nodup unique

end Belay.Sqlite
