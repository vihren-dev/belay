import Belay.Sqlite.Model.DerivedColumnRows
import Belay.Sqlite.Model.ScanRowMap
import Belay.Sqlite.Model.PlainUpdateEffect

set_option doc.verso true

/-! The table that a successful backfill of an appended column leaves, and its scan (ADR 0017, S6).
The backfill is a plain UPDATE that assigns an expression of the old cells to the appended column. The
laws read the rows and the scan from the actual effect of the UPDATE, not from an assumed row relation. -/

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

/-- For every database whose table at the target has the old table's columns with the appended column and
NULL in each row, every successful plain UPDATE that assigns an expression of the old columns to the
appended column leaves the target with the same shape and the old rows with the stored value of the
expression appended. The target must have storage, the old rows must be wide and aliased, and the old
columns and the appended column must have no generated expression. The expression is evaluated in the
context of the statement. The conclusion holds under the supplied successful effect; it does not say that
the UPDATE succeeds. Proof sketch: the successful-effect law ({name}`table_after_update_ok`) gives the
computed table, and {name}`updated_derived_append` gives its rows. -/
theorem table_after_derived_update (clock : Int) (counters : Counters) (parameters : List Value)
    {database after : Database} {target : Nat} (table : Table) (column : CatalogColumn) (derived : Expr)
    (present : database.table target = some (table.appendColumns [(column, .null)]))
    (aligned : target < database.rows.length)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (below : derived.readsBelow table.shape.columns.length = true)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none) (newPlain : column.generated = none)
    (success : (runStatement clock counters parameters
      (.update target [(table.shape.columns.length, derived)] none [] [] none) database).effect = .ok after) :
    after.table target = some
      { shape := { table.shape with columns := table.shape.columns ++ [column] },
        rows := table.rows.map fun row => row.appendValues
          [Value.store column.affinity
            (derived.eval (statementContext clock counters parameters database []) row.values)] } := by
  rw [table_after_update_ok clock counters parameters _ none [] [] present aligned success]
  exact congrArg (fun rows : List Row => some
    ({ shape := { table.shape with columns := table.shape.columns ++ [column] }, rows } : Table))
    (updated_derived_append (statementContext clock counters parameters database [])
      (statementContext_nil_rowFree clock counters parameters database) table column derived wide aliased below
      plain newPlain)

/-- Under the premises of {name}`table_after_derived_update` and with the primary-key positions of the old
table inside its columns, the source rows of the target after the UPDATE are the source rows of the old
table with the stored value of the expression appended to each. Rowid order and {lit}`WITHOUT ROWID` order,
with direction and collation, are those of the old table, and the old rows can have any order. Proof
sketch: the effect identifies the actual stored table, then {name}`sourceRows_updated_derived` transports
its scan. -/
theorem sourceRows_after_derived_update (clock : Int) (counters : Counters) (parameters : List Value)
    {database after : Database} {target : Nat} (table : Table) (column : CatalogColumn) (derived : Expr)
    (present : database.table target = some (table.appendColumns [(column, .null)]))
    (aligned : target < database.rows.length)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (below : derived.readsBelow table.shape.columns.length = true)
    (keysInside : ∀ position ∈ table.shape.primaryKey, position < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none) (newPlain : column.generated = none)
    (success : (runStatement clock counters parameters
      (.update target [(table.shape.columns.length, derived)] none [] [] none) database).effect = .ok after) :
    (after.table target).map sourceRows = some
      ((sourceRows table).map fun cells => cells ++
        [Value.store column.affinity
          (derived.eval (statementContext clock counters parameters database []) cells)]) := by
  rw [table_after_update_ok clock counters parameters _ none [] [] present aligned success]
  simp only [Option.map_some]
  rw [sourceRows_updated_derived _ (statementContext_nil_rowFree clock counters parameters database) table column
    derived wide aliased below keysInside plain newPlain]

end Belay.Sqlite.Model
