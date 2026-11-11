import Belay.Sqlite.Model.Queries.Select.FromSubquerySelectResolution

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The scope of a subquery of one table inside a query of one table: the scope {lit}`outer` of the query around it,
one depth further out, followed by the scope {lit}`inner` of its own table, whose first cell is at {lit}`start`, the
number of cells of the query around it. It is the scope that {lit}`resolveSelect` gives the subquery, for the scopes of two
tables that the catalog has ({name}`tableScope`). -/
def correlatedScope (outer inner : Scope) (start : Nat) : Scope :=
  Scope.enclose outer (inner.map fun source => { source with offset := start })

/-- The scope of a table that the catalog has at a position has the columns of the table, so its width is the number of
columns. Proof sketch: the definitions compute ({name}`Scope.columns_singleAt`). -/
theorem tableScope_columns_length (catalog : Catalog) (reference : Syntax.TableReference) (position : Nat)
    (table : CatalogTable) : (tableScope catalog reference position table).columns.length = table.columns.length := by
  simp [tableScope, Scope.columns_singleAt]

end Belay.Sqlite.Model
