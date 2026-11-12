import Belay.Sqlite.Model.Schema.Dispatch.CorrelatedSubquerySource
import Belay.Sqlite.Model.Schema.Dispatch.SelectSubqueryRules
import Belay.Sqlite.Model.Queries.Evaluation.CorrelatedSubqueryRun

set_option doc.verso true

/-! The run of a simple subquery of one table for one row of an outer query (task 20261027). A subquery row is the
outer row followed by the cells of a row of the subquery's table, so a subquery reads the outer cells at their own
positions and its own cells after the width {lit}`outer` of the outer query. The module is general over the table
position, the width, an optional {lit}`WHERE` expression and the result expressions, so it covers
{lit}`SELECT c FROM u`, {lit}`SELECT 1 FROM u WHERE u.c = x`, a subquery with a {lit}`WHERE` clause, and any result
expression. It has no fact about a catalog. -/

namespace Belay.Sqlite.Model.Resolved

/-- The rows of a subquery of one table for one outer row, before the condition: each row of the table in scan order after
the outer cells ({name}`outerCells`) of the width {lit}`outer`. -/
def joinedRows (outer : Nat) (outerRow : List Value) (table : Table) : List (List Value) :=
  (sourceRows table).map fun cells => outerCells outer outerRow ++ cells

/-- For every outer row, every database with the table at the position, every context and optional initial
database, the subquery {name}`Query.oneTable` run for the outer row has, as its rows, one row for each joined row
({name}`joinedRows`) that the condition keeps ({name}`conditionKeeps`), with the values of the result expressions; it
has no fault, and its rows are certain. The expressions read the outer cells followed by the cells of the table row.
The outer row can have any length: the subquery sees it cut or filled with NULL to the width {lit}`outer`. The premises
are that no expression has a fallible call ({lit}`plain`) and that none has a fault over the empty row and over each
joined row ({lit}`faultless`); a premise that fails is not assumed. Proof sketch: the source rows are the joined rows
({name}`Query.sourceAfter_first`); the query has no fault ({name}`Query.subqueryRun_of_faultless`); its result is
the filtered rows with the result expressions ({name}`Query.results_plain_unordered`). -/
theorem Query.oneTable_subqueryRun (context : EvalContext) (database : Database) (initial : Option Database)
    (position outer : Nat) (condition : Option Expr) (projections : List Expr) (names : List String) (table : Table)
    (outerRow : List Value) (present : database.table position = some table)
    (plain : ∀ expression ∈ condition.toList ++ projections, expression.any Expr.isFallibleCall = false)
    (faultless : ∀ row ∈ [] :: joinedRows outer outerRow table,
      ∀ expression ∈ condition.toList ++ projections, (expression.evaluate context row).2 = .none) :
    ((Query.oneTable position outer condition projections names).subqueryRun context database outerRow initial).rows =
        ((joinedRows outer outerRow table).filter (conditionKeeps condition context)).map (fun row =>
          projections.map (fun expression => expression.eval context row)) ∧
      ((Query.oneTable position outer condition projections names).subqueryRun context database outerRow
        initial).fault = .none ∧
      ((Query.oneTable position outer condition projections names).subqueryRun context database outerRow
        initial).rowsCertain = true := by
  have found := Query.sourceAfter_first context database initial (Query.oneTable position outer condition projections names)
    position table outerRow rfl present
  have run := Query.subqueryRun_of_faultless context database outerRow initial rfl rfl rfl found rfl
    (List.all_eq_true.mpr fun expression inside => by
      rw [Query.oneTable_expressions] at inside
      simp [plain expression inside])
    (fun row member expression inside => by
      rw [Query.oneTable_expressions] at inside
      exact faultless row member expression inside) rfl rfl
  rw [run]
  refine ⟨?_, rfl, by dsimp only; exact Query.windowCertain_whole context rfl _ _⟩
  rw [Query.results_plain_unordered context rfl rfl rfl rfl rfl rfl]
  unfold Query.rowOutput
  simp [filtered, joinedRows, Query.oneTable, Query.simple, Function.comp_def]
  rfl

end Belay.Sqlite.Model.Resolved
