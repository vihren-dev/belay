import Belay.Sqlite.Model.AdmittedUpdateRows
import Belay.Sqlite.Model.DatabaseFacts
import Belay.Sqlite.Model.ExprAppendLaws
import Belay.Sqlite.Model.RowUpdate

set_option doc.verso true

/-! The row effect of backfilling an appended column from an expression (ADR 0017, S6). The
migration adds a column, which holds NULL in every row, and then assigns to it a value derived from
the other cells of the same row. These laws use the existing assignment evaluator
({lit}`LiteralData.assign`). Their structural premises exclude generated-cell effects; the effect of
the whole statement and its triggers are separate laws. -/

namespace Belay.Sqlite.Model
open Resolved

/-- For every context whose subqueries do not depend on the outer row, columns without a generated
column, appended column without a generated expression, row with exactly as many cells as the columns, and
expression that reads only cells below the number of columns: assigning the appended cell to the
expression gives the row with one appended cell, which is the value of the expression stored with the
affinity of the appended column. Every old cell and the rowid stay. In plain words, the backfill of a
derived column writes {lit}`store(affinity, expression(row))` and changes nothing else. The expression can
be any expression of the old cells, so {lit}`lower` of one column, a concatenation and an integer
sum are instances. Proof sketch: generated-cell evaluation is the identity, the expression reads the same
value over the row with the NULL cell appended ({name}`Expr.eval_append`), and the one assignment replaces
the appended NULL. -/
theorem assign_derived_append (context : EvalContext) (rowFree : context.RowFree)
    (columns : List CatalogColumn) (column : CatalogColumn) (row : Row) (derived : Expr)
    (wide : row.values.length = columns.length) (below : derived.readsBelow columns.length = true)
    (plain : ∀ old ∈ columns, old.generated = none) (newPlain : column.generated = none) :
    LiteralData.assign context (columns ++ [column]) [(columns.length, derived)] (row.appendValues [.null]) =
      row.appendValues [Value.store column.affinity (derived.eval context row.values)] := by
  have allPlain : ∀ old ∈ columns ++ [column], old.generated = none := by
    intro old member
    rcases List.mem_append.mp member with before | added
    · exact plain old before
    · rcases List.mem_singleton.mp added with rfl
      exact newPlain
  have same : derived.eval context (row.values ++ [Value.null]) = derived.eval context row.values :=
    Expr.eval_append context rowFree row.values [.null] (Nat.le_of_eq wide.symm) below
  have affinity : LiteralData.positionAffinity (columns ++ [column]) columns.length = column.affinity := by
    simp [LiteralData.positionAffinity]
  unfold LiteralData.assign LiteralData.assignFrom
  rw [LiteralData.generatedCells_plain _ _ allPlain]
  simp only [Row.appendValues, List.foldl_cons, List.foldl_nil, same, affinity]
  simp [← wide, List.set_append_right]

/-- For every context whose subqueries do not depend on the outer row, table with wide aliased rows
and no generated column, appended column without a generated expression, and expression that reads only
the old columns: adding the column with NULL and backfilling it from the expression maps each original
row to that row with the stored value of the expression appended. The row order and the original rowids
stay. Proof sketch: the UPDATE maps each row; the assignment law ({name}`assign_derived_append`) and the
alias law ({name}`LiteralData.movedRowid_append`) identify each image. -/
theorem updated_derived_append (context : EvalContext) (rowFree : context.RowFree) (table : Table)
    (column : CatalogColumn) (derived : Expr)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (below : derived.readsBelow table.shape.columns.length = true)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none) (newPlain : column.generated = none) :
    (LiteralData.updated context (table.appendColumns [(column, .null)])
      [(table.shape.columns.length, derived)] none).rows =
      table.rows.map (fun row =>
        row.appendValues [Value.store column.affinity (derived.eval context row.values)]) := by
  simp only [LiteralData.updated, Table.appendColumns, List.map_cons, List.map_nil,
    Value.store_null, List.map_map]
  apply List.map_congr_left
  intro row member
  simp only [Function.comp_apply, LiteralData.selected, Option.all_none, ite_true]
  rw [assign_derived_append context rowFree table.shape.columns column row derived
    (wide row member) below plain newPlain]
  exact LiteralData.movedRowid_append table.shape.rowidAlias row _ (aliased row member)

end Belay.Sqlite.Model
