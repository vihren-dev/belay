import Belay.Sqlite.Model.Shared.Catalog.CatalogObjects

namespace Belay.Sqlite.Model.Conformance

/-- The {lit}`hidden` value of {lit}`PRAGMA table_xinfo` for a catalog column: 2 for a
{lit}`VIRTUAL` and 3 for a {lit}`STORED` generated column, else 0. -/
def columnHidden (column : CatalogColumn) : Nat :=
  match column.generated with
  | some { stored := true, .. } => 3
  | some { stored := false, .. } => 2
  | none => 0

end Belay.Sqlite.Model.Conformance
