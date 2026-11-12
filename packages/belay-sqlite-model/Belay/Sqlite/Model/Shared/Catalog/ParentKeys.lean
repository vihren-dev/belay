import Belay.Sqlite.Model.Shared.Catalog.Catalog

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The table at a catalog position, or {lean}`(none : Option CatalogTable)` for a
non-table object or a position past the end. -/
def Catalog.tableAt (catalog : Catalog) (position : Nat) : Option CatalogTable :=
  match catalog[position]? with
  | some { entry := .table table, .. } => some table
  | some { entry := .index _, .. } | some { entry := .view _, .. } | some { entry := .trigger _, .. } => none
  | none => none

end Belay.Sqlite.Model
