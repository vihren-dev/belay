import Belay.Sqlite.Model.Schema.Dispatch.SelectCalmRule
import Belay.Sqlite.Model.Schema.Writes.AdmittedCellLaws
import Belay.Sqlite.Model.Queries.Evaluation.ExprEvalLaws
import Belay.Sqlite.Model.Queries.Evaluation.CountOf
import Belay.Sqlite.Model.Queries.Evaluation.ComparisonLaws
import Belay.Sqlite.Model.Schema.Ddl.CatalogSpec

set_option doc.verso true

/-!
The rows of a table after a plain INSERT adds one row (ADR 0017, S6). A scan of a table
sees its rows in some order, so the claims here speak of membership and counts, which do not
depend on the order. They serve the universal claims about an INSERT: a row that no earlier row
matches and that the new row matches is the only match. The module also states what the resolved
row of a two-parameter INSERT is and when the condition {lit}`column = ?n` holds for a row.
-/

namespace Belay.Sqlite.Model

/-- For every table without a generated column whose rowid alias is absent or the first column, and
every row whose first cell is an integer: the rows after inserting it are the old rows and one row
with the cells as supplied. The rowid is {name}`LiteralData.newRowid`. Proof sketch: the alias cell
is already the integer rowid and no generated column changes a cell. -/
theorem LiteralData.inserted_plain (table : Table) (first : Int) (rest : List Value)
    (noGenerated : ∀ column ∈ table.shape.columns, column.generated = none)
    (alias : table.shape.rowidAlias = none ∨ table.shape.rowidAlias = some 0) :
    (LiteralData.inserted table [.integer first :: rest]).rows =
      table.rows ++ [⟨LiteralData.newRowid table (.integer first :: rest), .integer first :: rest⟩] := by
  simp only [LiteralData.inserted, LiteralData.insertRow, List.foldl_cons, List.foldl_nil, LiteralData.newCells]
  rw [LiteralData.generatedCells_plain _ _ noGenerated]
  rcases alias with none | some
  · simp [none]
  · have : LiteralData.newRowid table (.integer first :: rest) = first := by
      simp [LiteralData.newRowid, some]
    simp [some, this]

/-- For every raw database, position below the number of its row lists and rows: the rows at the
position, after {name}`Database.setRows` at it, are the supplied rows. Proof sketch:
{lit}`List.set` stores the rows at a position below the length. -/
theorem Database.rows_getD_setRows {raw : Database} {position : Nat} (rows : List Row)
    (aligned : position < raw.rows.length) : (raw.setRows position rows).rows.getD position [] = rows := by
  simp [Database.setRows, List.getD_eq_getElem?_getD, List.getElem?_set_self aligned]

/-- For every raw database whose row lists match its catalog, and every table that the lookup of the
catalog finds: the position of the table is below the number of row lists. Proof sketch: the lookup
gives an object of the catalog at the position, so the position is below the length of the catalog,
which is the length of the row lists. -/
theorem Database.position_lt_rows {raw : Database} (shaped : raw.RowsShaped) {name : Identifier}
    {position : Nat} {table : CatalogTable} (found : raw.catalog.findTable name = some (position, table)) :
    position < raw.rows.length := by
  obtain ⟨object, atPosition, -⟩ := Catalog.findTable_some _ _ _ _ found
  rw [shaped.1]
  exact (List.getElem?_eq_some_iff.1 atPosition).1

/-- For every clock value, counters, two bound values and two columns: the row that a plain INSERT
with the two parameters supplies is the two bound values, each stored with the affinity of its
column. Proof sketch: the parameters of the context are the bound values. -/
theorem rowsAt_two_parameters (value : Int) (counters : Counters) (database : Database)
    (first second : CatalogColumn) (a b : Value) :
    Resolved.rowsAt (Resolved.statementContext value counters [a, b] database []) [first, second]
      [[.expression (.parameter 1), .expression (.parameter 2)]] =
      [[Value.store first.affinity (boundValue a), Value.store second.affinity (boundValue b)]] := by
  simp [Resolved.rowsAt, Resolved.Cell.valueAt, List.zipIdx, Resolved.Expr.eval_parameter, parameterValue, Resolved.statementContext,
    Resolved.subqueryContext]

/-- For every counters, database and three values: the resolved row of an INSERT of the three
parameters {lit}`?1`, {lit}`?2` and {lit}`?3` into a table with three columns is the one row of
the three values that each column stores under its affinity. Proof sketch: unfold the row, the
cells and the three parameters. -/
theorem rowsAt_three_parameters (value : Int) (counters : Counters) (database : Database)
    (first second third : CatalogColumn) (a b c : Value) :
    Resolved.rowsAt (Resolved.statementContext value counters [a, b, c] database []) [first, second, third]
      [[.expression (.parameter 1), .expression (.parameter 2), .expression (.parameter 3)]] =
      [[Value.store first.affinity (boundValue a), Value.store second.affinity (boundValue b),
        Value.store third.affinity (boundValue c)]] := by
  simp [Resolved.rowsAt, Resolved.Cell.valueAt, List.zipIdx, Resolved.Expr.eval_parameter, parameterValue,
    Resolved.statementContext, Resolved.subqueryContext]

/-- For every table without a generated column whose rowid alias is absent or at one position, every
supplied cells, every rowid and every other position: the cell of the new row at the other position
is the supplied cell. Proof sketch: no generated column changes a cell, and only the alias position
may change to the rowid. -/
theorem LiteralData.newCells_getElem?_of_plain (table : Table) (values : List Value) (rowid : Int)
    (noGenerated : ∀ column ∈ table.shape.columns, column.generated = none)
    {position : Nat} (alias : table.shape.rowidAlias = none ∨ table.shape.rowidAlias = some position)
    {other : Nat} (different : other ≠ position) :
    (LiteralData.newCells table values rowid)[other]? = values[other]? := by
  unfold LiteralData.newCells
  rw [LiteralData.generatedCells_plain _ _ noGenerated]
  rcases alias with none | some
  · simp [none]
  · simp [some, List.getElem?_set_ne (Ne.symm different)]

/-- For every table and every cells: the rows after inserting one row are the old rows and one new
row, whose rowid is {name}`LiteralData.newRowid` and whose cells are {name}`LiteralData.newCells`.
Proof sketch: unfold the insertion of a single row. -/
theorem LiteralData.inserted_single_rows (table : Table) (values : List Value) :
    (LiteralData.inserted table [values]).rows = table.rows ++
      [⟨LiteralData.newRowid table values,
        LiteralData.newCells table values (LiteralData.newRowid table values)⟩] := by
  simp [LiteralData.inserted, LiteralData.insertRow]

end Belay.Sqlite.Model
