import Belay.Sqlite.Model.Schema.Columns.DerivedColumnTable
import Belay.Sqlite.Model.Programs.Scripts.PlainUpdateRule

set_option doc.verso true

namespace Belay.Sqlite.Model
open Resolved

/-- Storing the result of a context-free assignment to a newly appended NULL column
gives the rows of {name}`Table.addDerivedColumn` on the original wide, aliased table.
The old and new columns must have no generated expression, and the assignment reads
only old columns. The write publishes its own counters. Proof sketch: substitute
{name}`updated_derived_append` and move each evaluation to the canonical context. -/
theorem Connection.afterWrite_backfill (connection : Connection) (position : Nat) (counts : Counts)
    {eval : EvalContext} (rowFree : eval.RowFree) (table : Table) {column : CatalogColumn} {expr : Resolved.Expr}
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (below : expr.readsBelow table.shape.columns.length = true)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none) (newPlain : column.generated = none)
    (contextFree : expr.ContextFree) :
    ∃ counters, connection.afterWrite (connection.state.database.setRows position
      (LiteralData.updated eval (table.appendColumns [(column, .null)]) [(table.shape.columns.length, expr)] none).rows) counts =
      { connection with state := { connection.state with
        database := connection.state.database.setRows position (table.addDerivedColumn column expr).rows, counters } } := by
  rw [updated_derived_append eval rowFree table column expr wide aliased below plain newPlain]
  have rows : table.rows.map (fun row => row.appendValues [Value.store column.affinity (expr.eval eval row.values)]) =
      (table.addDerivedColumn column expr).rows := by
    simp only [Table.addDerivedColumn]
    exact List.map_congr_left fun row _ => by rw [contextFree]
  rw [rows]
  exact ⟨_, rfl⟩

end Belay.Sqlite.Model
