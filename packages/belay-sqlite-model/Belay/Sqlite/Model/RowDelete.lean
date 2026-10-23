import Belay.Sqlite.Model.RowUpdate

set_option doc.verso true

/-! The execution of DELETE (ADR 0012, amendment 1, slice 3c): the filter is evaluated on
each row, as for UPDATE ({lit}`LiteralData.selected`), and the selected rows are removed. -/

namespace Belay.Sqlite.Model
namespace LiteralData

/-- Remove every row that {name}`selected` accepts; without a filter, every row. The
other rows keep their rowids, cells and order, and the shape does not change. With
{lean}`(none : Option Resolved.Expr)` as the filter the result has no rows. -/
def deleted (context : Resolved.EvalContext) (table : Table) (filter : Option Resolved.Expr) : Table :=
  { table with rows := table.rows.filter fun row => !selected context filter row }

end LiteralData
end Belay.Sqlite.Model
