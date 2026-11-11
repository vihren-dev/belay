import Belay.Sqlite.Model.Schema.Writes.DerivedColumnRows
import Belay.Sqlite.Model.Queries.Evaluation.ScanRowMap
import Belay.Sqlite.Model.Schema.Dispatch.Subqueries

set_option doc.verso true

namespace Belay.Sqlite.Model
open Resolved

/-- For every clock value, counters and parameters, the context of a statement without subqueries does
not depend on the outer row ({name}`EvalContext.RowFree`). Proof sketch: it is the plain context with
the counters and the parameters, which has the plain subqueries. -/
theorem statementContext_nil_rowFree (clock : Int) (counters : Counters) (parameters : List Value)
    (database : Database) : (statementContext clock counters parameters database []).RowFree :=
  EvalContext.plain_rowFree clock

/-- For every context whose subqueries do not depend on the outer row, table with wide aliased rows,
primary-key positions inside the columns and no generated column, appended column without a generated
expression, and expression that reads only the old columns: the source rows of the table that backfills
the appended column ({name}`LiteralData.updated`) are the source rows of the old table with the stored
value of the expression appended to each. Rowid order and {lit}`WITHOUT ROWID` order, with key direction
and collation, are those of the old table, whatever the order of the stored rows. Proof sketch: the rows
of the backfilled table are the old rows with a cell appended ({name}`updated_derived_append`); an
appended cell changes neither the rowid nor a key cell nor a key collation, so
{name}`sourceRows_map` transports the scan. -/
theorem sourceRows_updated_derived (context : EvalContext) (rowFree : context.RowFree) (table : Table)
    (column : CatalogColumn) (derived : Expr)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (below : derived.readsBelow table.shape.columns.length = true)
    (keysInside : ∀ position ∈ table.shape.primaryKey, position < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none) (newPlain : column.generated = none) :
    sourceRows (LiteralData.updated context (table.appendColumns [(column, .null)])
      [(table.shape.columns.length, derived)] none) =
      (sourceRows table).map fun cells => cells ++ [Value.store column.affinity (derived.eval context cells)] := by
  have result : LiteralData.updated context (table.appendColumns [(column, .null)])
      [(table.shape.columns.length, derived)] none =
      { shape := { table.shape with columns := table.shape.columns ++ [column] },
        rows := table.rows.map fun row =>
          row.appendValues [Value.store column.affinity (derived.eval context row.values)] } :=
    congrArg (fun rows : List Row =>
      ({ shape := { table.shape with columns := table.shape.columns ++ [column] }, rows } : Table))
      (updated_derived_append context rowFree table column derived wide aliased below plain newPlain)
  rw [result, sourceRows_map table { table.shape with columns := table.shape.columns ++ [column] }
    (fun row => row.appendValues [Value.store column.affinity (derived.eval context row.values)])
    rfl rfl rfl ?_ (fun _ _ => rfl) ?_]
  · simp [sourceRows, List.map_map, Row.appendValues, Function.comp_def]
  · intro position member
    simp [List.getElem?_append_left (keysInside position member)]
  · intro row member position inKey
    have inside : position < row.values.length := by rw [wide row member]; exact keysInside position inKey
    simp [Row.appendValues, List.getD_eq_getElem?_getD, List.getElem?_append_left inside]

end Belay.Sqlite.Model
