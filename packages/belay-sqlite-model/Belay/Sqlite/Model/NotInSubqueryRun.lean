import Belay.Sqlite.Model.NotInSubquerySource

set_option doc.verso true

/-! The run of the two subqueries of {lit}`x NOT IN (SELECT c FROM u)` and of the correlated
{lit}`NOT EXISTS (SELECT 1 FROM u WHERE u.c = x)` for one row of an outer query (task 20261027). A
subquery row is the outer row followed by the cells of a row of {lit}`u`, so the column {lit}`c` of {lit}`u` is
the cell at position {lit}`outer + c`, where {lit}`outer` is the width of the outer row. The module is general
over the table position, the columns and the width; it has no fact about a catalog. -/

namespace Belay.Sqlite.Model.Resolved

/-- The subquery {lit}`SELECT c FROM u` of an {lit}`IN` test, for an outer query whose rows have {lit}`outer` cells:
it has the table at {lit}`table` as its only source, no {lit}`WHERE`, and the column {lit}`column` of the
table as its one result column. The cells of the outer row come first, so the column is at position
{lit}`outer + column`. -/
def Query.columnOf (table outer column : Nat) (names : List String) : Query :=
  { Query.simple [QuerySource.first table] none [.scalar (.column (outer + column))] names with outer }

/-- The correlated subquery {lit}`SELECT 1 FROM u WHERE u.c = x`, for an outer query whose rows have {lit}`outer`
cells: it has the table at {lit}`table` as its only source, the condition that the column {lit}`column` of the
table equals the outer cell at position {lit}`key` under the affinity and the collation, and the result
column 1. As in SQLite's resolution of {lit}`u.c = x`, the table's column is the left operand. -/
def Query.matchingKey (table outer column key : Nat) (affinity : Option Affinity) (collation : Collation)
    (names : List String) : Query :=
  { Query.simple [QuerySource.first table]
      (some (.compare .eq affinity (.column (outer + column)) (.column key) collation))
      [.scalar (.literal (.integer 1))] names with outer }


/-- For every table position, widths, column and names, the query {name}`Query.columnOf` is simple
({name}`Query.Simple`). Proof sketch: it is {name}`Query.simple` with another width of the outer row. -/
theorem Query.columnOf_simple (table outer column : Nat) (names : List String) :
    (Query.columnOf table outer column names).Simple :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- For every table position, widths, column, names, affinity and collation, the query
{name}`Query.matchingKey` is simple ({name}`Query.Simple`). Proof sketch: it is {name}`Query.simple` with another
width of the outer row. -/
theorem Query.matchingKey_simple (table outer column key : Nat) (affinity : Option Affinity) (collation : Collation)
    (names : List String) : (Query.matchingKey table outer column key affinity collation names).Simple :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- The expressions of the query {name}`Query.columnOf` are the one cell of its column. Proof sketch: unfold the
expressions of the query; it has no condition and no argument of a source, and one result column. -/
theorem Query.columnOf_expressions (table outer column : Nat) (names : List String) :
    (Query.columnOf table outer column names).expressions = [.column (outer + column)] := by
  simp [Query.columnOf, Query.simple, Query.expressions, Query.keptExpressions, Output.scalars, Output.operands,
    QuerySource.expressions, QuerySource.first]

/-- The expressions of the query {name}`Query.matchingKey` are its condition and the literal 1 of its result column.
Proof sketch: as for {name}`Query.columnOf_expressions`. -/
theorem Query.matchingKey_expressions (table outer column key : Nat) (affinity : Option Affinity)
    (collation : Collation) (names : List String) :
    (Query.matchingKey table outer column key affinity collation names).expressions =
      [.compare .eq affinity (.column (outer + column)) (.column key) collation, .literal (.integer 1)] := by
  simp [Query.matchingKey, Query.simple, Query.expressions, Query.keptExpressions, Output.scalars, Output.operands,
    QuerySource.expressions, QuerySource.first]


/-- For every outer row, every database with the table at the position, and every context and optional initial
database, the subquery {lit}`SELECT c FROM u` ({name}`Query.columnOf`) run for the outer row has, as its rows, one row for
each row of the table in scan order, with the cell of the column {lit}`column` (NULL past the end of the row); it has no
fault, and its rows are certain. The outer row can have any length: the subquery sees it cut or filled with NULL to the
width {lit}`outer` ({name}`Query.outerCells`). Proof sketch: the source rows are the table rows after the outer cells
({name}`Query.sourceAfter_first`); the simple query has no fault ({name}`Query.subqueryRun_simple_after`); its result is
the cell at position {lit}`outer + column` of each joined row, which is the cell {lit}`column` of the table row because
the outer cells have {lit}`outer` cells ({name}`Query.outerCells_length`). -/
theorem Query.columnOf_subqueryRun (context : EvalContext) (database : Database) (initial : Option Database)
    (position outer column : Nat) (names : List String) (table : Table) (outerRow : List Value)
    (present : database.table position = some table) :
    ((Query.columnOf position outer column names).subqueryRun context database outerRow initial).rows =
        (sourceRows table).map (fun cells => [cells.getD column .null]) ∧
      ((Query.columnOf position outer column names).subqueryRun context database outerRow initial).fault = .none ∧
      ((Query.columnOf position outer column names).subqueryRun context database outerRow initial).rowsCertain =
        true := by
  have found := Query.sourceAfter_first context database initial (Query.columnOf position outer column names)
    position table outerRow rfl present
  have run := Query.subqueryRun_simple_after context database initial outerRow _
    (Query.columnOf_simple position outer column names) _ found rfl
    (by simp [Query.columnOf_expressions, Expr.any, Expr.isFallibleCall])
    (by simp [Query.columnOf_expressions, Expr.evaluate])
  rw [run]
  refine ⟨?_, rfl, rfl⟩
  rw [(Query.columnOf_simple position outer column names).results_eq]
  have length := Query.outerCells_length (Query.columnOf position outer column names) outerRow
  have cell : ∀ row : List Value, ((Query.columnOf position outer column names).outerCells outerRow ++ row).getD
      (outer + column) .null = row.getD column .null := fun row => by
    have := getD_append_length_add ((Query.columnOf position outer column names).outerCells outerRow) row column .null
    rwa [length] at this
  have noFilter : (Query.columnOf position outer column names).filter = none := rfl
  have columns : (Query.columnOf position outer column names).columns = [.scalar (.column (outer + column))] := rfl
  have keepAll : ∀ rows : List (List Value), rows.filter (fun _ => true) = rows := fun rows =>
    List.filter_eq_self.mpr (by simp)
  simp only [List.getD_eq_getElem?_getD] at cell
  simp [filtered, noFilter, columns, Expr.eval_column, cell, keepAll]

/-- For every outer row, every key position inside the width {lit}`outer`, every database with the table at the position, and
every context and optional initial database, the correlated subquery {lit}`SELECT 1 FROM u WHERE u.c = x`
({name}`Query.matchingKey`) run for the outer row has, as its rows, one row with the value 1 for each row of the table in
scan order for which the comparison of the column {lit}`column` with the outer cell {lit}`key` is true
({name}`equalsValue`, with the table's cell as the left operand); it has no fault, and its rows are certain. Proof
sketch: as for {name}`Query.columnOf_subqueryRun`; the condition reads the cell at position {lit}`outer + column` of the
joined row, which is the cell of the table row, and the cell at {lit}`key`, which is the cell of the outer row
({name}`Query.outerCells_getD`). -/
theorem Query.matchingKey_subqueryRun (context : EvalContext) (database : Database) (initial : Option Database)
    (position outer column key : Nat) (affinity : Option Affinity) (collation : Collation) (names : List String)
    (table : Table) (outerRow : List Value) (keyInside : key < outer)
    (present : database.table position = some table) :
    ((Query.matchingKey position outer column key affinity collation names).subqueryRun context database outerRow
        initial).rows =
        ((sourceRows table).filter (fun cells => truthy (equalsValue affinity collation (cells.getD column .null)
          (outerRow.getD key .null)))).map (fun _ => [.integer 1]) ∧
      ((Query.matchingKey position outer column key affinity collation names).subqueryRun context database outerRow
        initial).fault = .none ∧
      ((Query.matchingKey position outer column key affinity collation names).subqueryRun context database outerRow
        initial).rowsCertain = true := by
  have found := Query.sourceAfter_first context database initial
    (Query.matchingKey position outer column key affinity collation names) position table outerRow rfl present
  have run := Query.subqueryRun_simple_after context database initial outerRow _
    (Query.matchingKey_simple position outer column key affinity collation names) _ found rfl
    (by simp [Query.matchingKey_expressions, Expr.any, Expr.isFallibleCall])
    (by simp [Query.matchingKey_expressions, Expr.evaluate, Fault.join])
  rw [run]
  refine ⟨?_, rfl, rfl⟩
  rw [(Query.matchingKey_simple position outer column key affinity collation names).results_eq]
  have length := Query.outerCells_length (Query.matchingKey position outer column key affinity collation names) outerRow
  have cell := Query.outerCells_getD (Query.matchingKey position outer column key affinity collation names) outerRow
    (key := key) keyInside
  have tableCell : ∀ row : List Value, ((Query.matchingKey position outer column key affinity collation
      names).outerCells outerRow ++ row).getD (outer + column) .null = row.getD column .null := fun row => by
    have := getD_append_length_add ((Query.matchingKey position outer column key affinity collation
      names).outerCells outerRow) row column .null
    rwa [length] at this
  have outerCell : ∀ row : List Value, ((Query.matchingKey position outer column key affinity collation
      names).outerCells outerRow ++ row).getD key .null = outerRow.getD key .null := fun row => by
    rw [getD_append_of_lt _ _ (by rw [length]; exact keyInside), cell]
  have filter : (Query.matchingKey position outer column key affinity collation names).filter =
      some (.compare .eq affinity (.column (outer + column)) (.column key) collation) := rfl
  have columns : (Query.matchingKey position outer column key affinity collation names).columns =
      [.scalar (.literal (.integer 1))] := rfl
  simp only [List.getD_eq_getElem?_getD] at tableCell outerCell
  simp [filtered, filter, columns, Expr.eval_compare, Expr.eval_column, Expr.eval_literal, tableCell, outerCell,
    equalsValue, List.filter_map, Function.comp_def]

end Belay.Sqlite.Model.Resolved
