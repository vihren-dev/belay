import Belay.Sqlite.Model.ExceptSubqueryRun
import Belay.Sqlite.Model.NotInIntegerProbe
import Belay.Sqlite.Model.ExprEvalLaws

set_option doc.verso true

/-! The source rows of a subquery for one row of an outer query (task 20261027). A subquery row is the outer row
followed by the cells of a row of the subquery's table, so a subquery reads the outer cells at their own
positions and its own cells after the width {lit}`outer` of the outer query. The module gives the outer cells that a
subquery sees for any outer row, the source rows of a subquery of one table, and the run of a simple subquery over
them. It has no fact about a catalog. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every two lists, a position past the first list and a default, the cell of the joined list at the position
shifted by the length of the first list is the cell of the second list at the position. Proof sketch: the
cell is the optional element at the position, which {name}`List.getElem?_append_right` moves. -/
theorem getD_append_length_add {α : Type} (first second : List α) (position : Nat) (default : α) :
    (first ++ second).getD (first.length + position) default = second.getD position default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    ← List.getD_eq_getElem?_getD]

/-- For every two lists, a position inside the first list and a default, the cell of the joined list at the position
is the cell of the first list. Proof sketch: {name}`List.getElem?_append_left`. -/
theorem getD_append_of_lt {α : Type} (first second : List α) {position : Nat} (inside : position < first.length)
    (default : α) : (first ++ second).getD position default = first.getD position default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left inside, ← List.getD_eq_getElem?_getD]


/-- The cells of the outer row that a subquery sees ({name}`Query.sourceAfter`): the outer row cut at the width
{lit}`outer` of the query, or filled with NULL up to it. -/
def Query.outerCells (query : Query) (outerRow : List Value) : List Value :=
  outerRow.take query.outer ++ List.replicate (query.outer - outerRow.length) .null


/-- For every query and outer row, the outer cells that a subquery sees have exactly the width {lit}`outer` of the
query. Proof sketch: the row is cut at the width or filled with NULL up to it; arithmetic on the lengths. -/
theorem Query.outerCells_length (query : Query) (outerRow : List Value) :
    (query.outerCells outerRow).length = query.outer := by
  simp only [Query.outerCells, List.length_append, List.length_take, List.length_replicate]
  omega

/-- For every query, outer row and position inside the width {lit}`outer` of the query, the outer cells that a subquery
sees have at the position the cell of the outer row, or NULL past the end of the row. Proof sketch: inside the row
the cut keeps the cell; past the end both sides are NULL. -/
theorem Query.outerCells_getD (query : Query) (outerRow : List Value) {key : Nat} (inside : key < query.outer) :
    (query.outerCells outerRow).getD key .null = outerRow.getD key .null := by
  unfold Query.outerCells
  by_cases within : key < outerRow.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [List.length_take]; omega),
      List.getElem?_take_of_lt inside, ← List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : outerRow.length ≤ key)]
    by_cases past : outerRow.length ≤ query.outer
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.getElem?_replicate]
      split <;> rfl
    · omega

/-- For every query whose only source is the table at a position as an inner join without a condition, every
outer row, every database with that table, and every optional initial database, the source rows of the query
for the outer row are the rows of the table in scan order, each after the outer cells
({name}`Query.outerCells`), with no fault. Proof sketch: unfold the join of the one source; with
no condition every row of the table joins the one row of outer cells. -/
theorem Query.sourceAfter_first (context : EvalContext) (database : Database) (initial : Option Database)
    (query : Query) (position : Nat) (table : Table) (outerRow : List Value)
    (sources : query.sources = [QuerySource.first position]) (present : database.table position = some table) :
    query.sourceAfter context outerRow database initial =
      some { rows := (sourceRows table).map (fun cells => query.outerCells outerRow ++ cells)
             width := (query.outerCells outerRow).length + table.shape.columns.length
             fault := .none
             outer := query.outerCells outerRow } := by
  simp [Query.sourceAfter, Query.outerCells, sources, List.foldlM, QuerySource.join, QuerySource.first,
    QuerySource.joinTable, joinRows, joinRow, joinMatches, QuerySource.matches, bind, Option.bind, pure, present]


/-- For every simple query, every outer row, and every source of the query for that outer row without fault
({name}`Query.sourceAfter`), whose expressions have no fallible call and no fault over the empty row and over each source
row, the run as a subquery for the outer row ({name}`Query.subqueryRun`) has the one result of the query as its rows, no
fault, and certain rows; it ends done. It is {name}`Query.subqueryRun_simple` for a subquery that may read the
cells of the outer row. Proof sketch: as for {name}`Query.subqueryRun_simple`, with the source given for the outer row. -/
theorem Query.subqueryRun_simple_after (context : EvalContext) (database : Database) (initial : Option Database)
    (outerRow : List Value) (query : Query) (simple : query.Simple) (source : SourceRows)
    (found : query.sourceAfter context outerRow database initial = some source)
    (clean : source.fault = .none) (plain : query.expressions.all (!·.any Expr.isFallibleCall) = true)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate context row).2 = .none) :
    query.subqueryRun context database outerRow initial =
      { rows := query.results context source.rows, fault := .none,
        firstCertain := query.windowCertain context source.rows (some 1), rowsCertain := true, ending := .done } := by
  unfold Query.subqueryRun
  rw [found]
  simp only [simple.bindWindow context.parameters, simple.run_of_faultless context plain source.rows faultless, clean]
  simp [Fault.join, Fault.soften, Query.windowCertain, certainCut, simple.limit, simple.offset]


end Belay.Sqlite.Model.Resolved
