import Belay

set_option doc.verso true

/-! The guide's lowercase filters as instances of the general derived-column laws (ADR 0017, S6). The
guide stores {lit}`lower(source)` in a TEXT column and moves the lookup {lit}`WHERE lower(source) =
lower(?n)` to {lit}`WHERE stored = lower(?n)`. The model has no law that fixes the expression to
{lit}`lower`. This module states the two resolved filters and proves, from the general laws, the two
facts that make the move sound for this expression: TEXT affinity leaves lowercase results unchanged,
so the two filters keep the same rows. Later modules reuse these definitions. -/

namespace LowercaseFixture
open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- For every value, storing its lowercase text with TEXT affinity keeps that result. NULL stays NULL
and every other input gives TEXT. Proof sketch: case analysis on the five value constructors. -/
theorem store_lower (value : Value) :
    Value.store .text (mapText lowerByte value) = mapText lowerByte value := by
  cases value <;> rfl

/-- For every pair of values, TEXT comparison affinity leaves their lowercase results unchanged, also for
NULL and nontext inputs. Proof sketch: each lowercase result is NULL or TEXT, which TEXT affinity keeps. -/
theorem comparisonOperands_lower (left right : Value) :
    comparisonOperands (some .text) (mapText lowerByte left) (mapText lowerByte right) =
      (mapText lowerByte left, mapText lowerByte right) := by
  cases left <;> cases right <;> rfl

/-- For every context, row and expression, a one-argument {lit}`lower` call returns the lowercase text of
the value of the expression. Proof sketch: the call and its argument reduce to the text function. -/
theorem eval_lower (context : EvalContext) (row : List Value) (expression : Expr) :
    (Expr.scalar .lower (.cons expression .nil)).eval context row =
      mapText lowerByte (expression.eval context row) := rfl

/-- The written declaration of a plain TEXT column, without a default or other constraint. -/
def textDefinition (name : Identifier) : Syntax.ColumnDefinition :=
  { name, declaredType := some "TEXT", constraints := [] }

/-- The metadata of the plain TEXT declaration, with the strict typing mode of the table. The column has
BINARY collation and no generated expression. -/
def textColumn (name : Identifier) (strict : Bool) : CatalogColumn :=
  { name, declaredType := some "TEXT", strictType := if strict then some .text else none }

/-- For every name and strictness, the general column of the declaration ({name}`definedColumn`) is
{name}`textColumn`. Proof sketch: case analysis on the strictness. -/
theorem definedColumn_text (name : Identifier) (strict : Bool) :
    definedColumn strict (textDefinition name) = textColumn name strict := by
  cases strict <;> rfl

/-- For every name and strictness, the column has TEXT affinity. -/
theorem textColumn_affinity (name : Identifier) (strict : Bool) : (textColumn name strict).affinity = .text := by
  cases strict <;> rfl

/-- The original predicate {lit}`lower(column) = lower(parameter)`, with resolved column and one-based
parameter positions. Function results have neither affinity nor collation, so the comparison has default
BINARY collation. -/
def originalFilter (source parameter : Nat) : Expr :=
  .compare .eq none (.scalar .lower (.cons (.column source) .nil))
    (.scalar .lower (.cons (.parameter parameter) .nil))

/-- The translated predicate {lit}`stored = lower(parameter)`. The stored column gives TEXT affinity and
default BINARY collation; {lit}`stored` is the position of the appended column. -/
def storedFilter (stored parameter : Nat) : Expr :=
  .compare .eq (some .text) (.column stored) (.scalar .lower (.cons (.parameter parameter) .nil))

/-- For every context whose subqueries ignore the outer row, row with exactly {lit}`width` cells, source
and parameter position, reading the appended lowercase cell at position {lit}`width` gives the value of the
predicate that computes lowercase from the source cell. In plain words, the move from
{lit}`lower(source) = lower(?n)` to {lit}`stored = lower(?n)` changes no comparison, for any parameter
value. Proof sketch: {name}`Expr.eval_compare_stored_left`; its agreement premise holds because TEXT affinity
keeps both lowercase operands ({name}`comparisonOperands_text_of_stored`, {name}`store_lower`). -/
theorem storedFilter_append (context : EvalContext) (rowFree : context.RowFree) (row : List Value)
    (width source parameter : Nat) (wide : row.length = width) :
    (storedFilter width parameter).eval context
        (row ++ [mapText lowerByte (row.getD source .null)]) =
      (originalFilter source parameter).eval context row := by
  subst wide
  have general := Expr.eval_compare_stored_left context rowFree row .eq (some .text) none .binary .binary
    (.scalar .lower (.cons (.column source) .nil)) (.scalar .lower (.cons (.parameter parameter) .nil))
    (mapText lowerByte (row.getD source .null)) .text rfl
    (by simp [Expr.readsBelow, Expr.any, Expr.isColumnFrom, Arguments.any])
    (by
      simp only [compareValue, store_lower]
      rw [comparisonOperands_text_of_stored _ _ (store_lower _) (by rw [eval_lower]; exact store_lower _)])
  rw [store_lower] at general
  exact general

/-- For every context whose subqueries ignore the outer row, row, appended cells, and source and parameter
positions with the source inside the row, the original predicate has the same value on the row with cells
appended. Proof sketch: the column reads the same cell ({name}`Expr.eval_append`). -/
theorem originalFilter_append (context : EvalContext) (rowFree : context.RowFree) (row extra : List Value)
    (source parameter : Nat) (inside : source < row.length) :
    (originalFilter source parameter).eval context (row ++ extra) =
      (originalFilter source parameter).eval context row :=
  Expr.eval_append context rowFree row extra (Nat.le_refl _)
    (by simp [originalFilter, Expr.readsBelow, Expr.any, Expr.isColumnFrom, Arguments.any, inside])

/-- For every context whose subqueries ignore the outer row, equally wide rows and positions, the simple
query that selects an existing id column under the stored predicate, over the rows with their lowercase
cell appended, has the results of the query under the original predicate over the original rows. Plain
words: for every parameter value and every number of rows, the lookup of ids through the stored column
gives the ids of the lookup through {lit}`lower(source)`. Each new row must be the old row with its
computed lowercase cell; the theorem does not say that a migration produced those rows. Proof sketch:
{name}`Query.simple_results_agree` with {name}`storedFilter_append`. -/
theorem results_translate (context : EvalContext) (rowFree : context.RowFree) (rows : List (List Value))
    (beforeSources afterSources : List QuerySource) (width source id parameter : Nat)
    (wide : ∀ row ∈ rows, row.length = width) (idInside : id < width) :
    (Query.simple afterSources (some (storedFilter width parameter)) [.scalar (.column id)] ["id"]).results
        context (rows.map fun row => row ++ [mapText lowerByte (row.getD source .null)]) =
      (Query.simple beforeSources (some (originalFilter source parameter))
        [.scalar (.column id)] ["id"]).results context rows :=
  Query.simple_results_agree context rowFree rows _ beforeSources afterSources _ _ _ ["id"] ["id"] width
    (fun row member => Nat.le_of_eq (wide row member).symm)
    (by
      intro output member
      cases List.mem_singleton.mp member
      simp [Output.readsBelow, Expr.readsBelow, Expr.any, Expr.isColumnFrom, idInside])
    fun row member => by
      simp only [Option.all_some]
      rw [storedFilter_append context rowFree row width source parameter (wide row member)]

/-- For every context whose subqueries ignore the outer row, equally wide rows and positions with the
source inside the width, the original predicate query keeps its results after a lowercase cell is appended
to each row. The statement covers NULL and nontext cells and parameters. Proof sketch:
{name}`Query.simple_results_agree` with {name}`originalFilter_append`. -/
theorem results_preserve (context : EvalContext) (rowFree : context.RowFree) (rows : List (List Value))
    (beforeSources afterSources : List QuerySource) (width source id parameter : Nat)
    (wide : ∀ row ∈ rows, row.length = width) (sourceInside : source < width) (idInside : id < width) :
    (Query.simple afterSources (some (originalFilter source parameter)) [.scalar (.column id)] ["id"]).results
        context (rows.map fun row => row ++ [mapText lowerByte (row.getD source .null)]) =
      (Query.simple beforeSources (some (originalFilter source parameter))
        [.scalar (.column id)] ["id"]).results context rows :=
  Query.simple_results_agree context rowFree rows _ beforeSources afterSources _ _ _ ["id"] ["id"] width
    (fun row member => Nat.le_of_eq (wide row member).symm)
    (by
      intro output member
      cases List.mem_singleton.mp member
      simp [Output.readsBelow, Expr.readsBelow, Expr.any, Expr.isColumnFrom, idInside])
    fun row member => by
      simp only [Option.all_some]
      rw [originalFilter_append context rowFree row _ source parameter (by rw [wide row member]; exact sourceInside)]

end LowercaseFixture
