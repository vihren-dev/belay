import Belay.Sqlite.Model.Shared.Catalog.Catalog

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The number of positions below the position that the drop keeps: the new position of a
kept object. For example, {lean}`keptBelow [1] 3 = 2`: dropping position 1 moves position 3
to position 2. A list with repeated positions counts each position once. -/
def keptBelow (positions : List Nat) (position : Nat) : Nat :=
  ((List.range position).filter fun below => !positions.contains below).length

/-- The entry with its catalog positions after the drop: an index names the new position
of its table ({name}`keptBelow`). Tables, views and triggers have no catalog positions. -/
def CatalogEntry.afterDrop (positions : List Nat) : CatalogEntry → CatalogEntry
  | .table shape => .table shape
  | .view definition => .view definition
  | .index found => .index { found with table := keptBelow positions found.table }
  | .trigger found => .trigger found

/-- The catalog without the objects at the positions, in catalog order, each kept object
with its catalog positions after the drop ({name}`CatalogEntry.afterDrop`). Positions past
the end change nothing, and {lean}`([] : List Nat)` keeps the catalog as it is. -/
def Catalog.drop (catalog : Catalog) (positions : List Nat) : Catalog :=
  (catalog.zipIdx.filter fun (_, position) => !positions.contains position).map fun (object, _) =>
    { object with entry := object.entry.afterDrop positions }

end Belay.Sqlite.Model
