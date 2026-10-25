import Belay.Sqlite.Model.AdmittedCellLaws
import Belay.Sqlite.Model.DatabaseFacts
import Belay.Sqlite.Model.ExprEvalLaws
import Belay.Sqlite.Model.RowUpdate

set_option doc.verso true

/-! The row effect of backfilling an appended TEXT field with {lit}`lower`.
These laws use the existing assignment evaluator. Their structural premises
exclude generated-cell effects; statement and trigger effects are separate. -/

namespace Belay.Sqlite.Model.NormalizedField
open Resolved

/-- For every value, storing its lowercase text with TEXT affinity keeps that
result. NULL stays NULL; every non-NULL input produces TEXT. Proof sketch:
case analysis on the five value constructors. -/
theorem store_lower (value : Value) :
    Value.store .text (mapText lowerByte value) = mapText lowerByte value := by
  cases value <;> rfl

/-- For every pair of values, TEXT comparison affinity leaves their lowercase
results unchanged. This includes NULL and all nontext inputs. Proof sketch:
each lowercase result is NULL or TEXT, which TEXT affinity preserves. -/
theorem comparisonOperands_lower (left right : Value) :
    comparisonOperands (some .text) (mapText lowerByte left) (mapText lowerByte right) =
      (mapText lowerByte left, mapText lowerByte right) := by
  cases left <;> cases right <;> rfl

/-- For every context, row and expression, a one-argument {lit}`lower` call
returns the lowercase text of that expression's value. Proof sketch: the scalar
call and its single argument reduce to the existing text function. -/
theorem eval_lower (context : EvalContext) (row : List Value) (expression : Expr) :
    (Expr.scalar .lower (.cons expression .nil)).eval context row =
      mapText lowerByte (expression.eval context row) := rfl

/-- For every column list with no generated column and every cell list,
generated-cell evaluation preserves the cell list exactly. Proof sketch:
the existing invariant law has no possible generated-cell update. -/
theorem generatedCells_plain (columns : List CatalogColumn) (values : List Value)
    (plain : ∀ column ∈ columns, column.generated = none) :
    LiteralData.generatedCells columns values = values := by
  apply LiteralData.generatedCells_invariant (fun cells => cells = values) rfl
  intro cells position column value found generated _
  simp [plain column (List.mem_of_getElem? found)] at generated

/-- For every aliased row, appending any cells and then applying alias movement
keeps the extended row. Without an alias, the premise imposes nothing.
Proof sketch: an existing alias position still contains the original integer
rowid after appending cells, so alias movement writes the same rowid. -/
theorem movedRowid_append (alias : Option Nat) (row : Row) (extra : List Value)
    (aliased : row.Aliased alias) :
    LiteralData.movedRowid alias (row.appendValues extra) = row.appendValues extra := by
  cases alias with
  | none => rfl
  | some position =>
    have cell := aliased position rfl
    have below := (List.getElem?_eq_some_iff.mp cell).1
    simp [LiteralData.movedRowid, Row.appendValues, List.getElem?_append_left below, cell]

/-- For every wide row, original plain columns, appended plain TEXT column and
existing source-column position, assigning the appended cell to {lit}`lower`
of that source cell gives exactly the original row with its lowercase value
appended. Every original cell and the rowid remain unchanged. Proof sketch:
generated-cell evaluation is identity, the source reads its original cell,
and the sole assignment replaces the appended NULL with the stored lowercase
value. -/
theorem assign_lower_append (context : EvalContext) (columns : List CatalogColumn)
    (column : CatalogColumn) (row : Row) (source : Nat)
    (wide : row.values.length = columns.length)
    (inside : source < columns.length)
    (plain : ∀ old ∈ columns, old.generated = none)
    (newPlain : column.generated = none) (text : column.affinity = .text) :
    LiteralData.assign context (columns ++ [column])
      [(columns.length, .scalar .lower (.cons (.column source) .nil))]
      (row.appendValues [.null]) =
        row.appendValues [mapText lowerByte (row.values.getD source .null)] := by
  have allPlain : ∀ old ∈ columns ++ [column], old.generated = none := by
    intro old member
    rcases List.mem_append.mp member with before | added
    · exact plain old before
    · rcases List.mem_singleton.mp added with rfl
      exact newPlain
  have oldCell : (row.values ++ [Value.null]).getD source .null = row.values.getD source .null := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : source < row.values.length)]
  have affinity : LiteralData.positionAffinity (columns ++ [column]) columns.length = .text := by
    simp [LiteralData.positionAffinity, text]
  unfold LiteralData.assign LiteralData.assignFrom
  rw [generatedCells_plain _ _ allPlain]
  simp only [Row.appendValues, List.foldl_cons, List.foldl_nil, eval_lower,
    Expr.eval_column, oldCell, affinity, store_lower]
  simp [← wide, List.set_append_right]

/-- For every table with wide aliased rows and no generated column, adding a
plain TEXT column with NULL and backfilling it from an existing column maps
each original row to that row with its lowercase source value appended.
The row order and original rowids are preserved. Proof sketch: the existing
UPDATE maps each row; the exact assignment and alias laws identify each image. -/
theorem updated_lower_append (context : EvalContext) (table : Table)
    (column : CatalogColumn) (source : Nat)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (inside : source < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none)
    (newPlain : column.generated = none) (text : column.affinity = .text) :
    (LiteralData.updated context (table.appendColumns [(column, .null)])
      [(table.shape.columns.length, .scalar .lower (.cons (.column source) .nil))] none).rows =
      table.rows.map (fun row => row.appendValues [mapText lowerByte (row.values.getD source .null)]) := by
  simp only [LiteralData.updated, Table.appendColumns, List.map_cons, List.map_nil,
    Value.store_null, List.map_map]
  apply List.map_congr_left
  intro row member
  simp only [Function.comp_apply, LiteralData.selected, Option.all_none, ite_true]
  rw [assign_lower_append context table.shape.columns column row source
    (wide row member) inside plain newPlain text]
  exact movedRowid_append table.shape.rowidAlias row _ (aliased row member)

end Belay.Sqlite.Model.NormalizedField
