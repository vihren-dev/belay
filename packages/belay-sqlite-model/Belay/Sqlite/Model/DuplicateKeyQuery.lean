import Belay.Sqlite.Model.SimpleResultsLaws
import Belay.Sqlite.Model.CountQueryLaws
import Belay.Sqlite.Model.IntegerCompareLaws
import Belay.Sqlite.Model.ExprEvalLaws
import Belay.Sqlite.Model.SimpleSubqueryRun

set_option doc.verso true

/-! The duplicate-key query of ADR 0017, S4 and S6: {lit}`SELECT c FROM t [WHERE w] GROUP BY k HAVING count(*) > 1`. It
keeps the rows of the table for which {lit}`w` is true, groups them by the key {lit}`k` under a collation and keeps
the groups of more than one row, so it has a row exactly when two such rows have a key that is equal under the
collation. NULL keys are equal here, unlike in a {lit}`UNIQUE` index. The query without {lit}`WHERE` and with the
result column {lit}`1` is the query of S4. -/

namespace Belay.Sqlite.Model.Resolved

/-- The duplicate-key query of the given sources, optional {lit}`WHERE` condition, result column with its name, grouping
key and collation: an aggregate query with the one grouping term, the one result column, the one aggregate
{lit}`count(*)` and the condition {lit}`HAVING count(*) > 1`, and without ordering, window, {lit}`DISTINCT` or
compound, that reads no cell of an outer query. The result column is the literal one named {lit}`"1"` for the query
of S4, and a grouped expression such as the key for the query of the guide. -/
def Query.duplicateKeys (sources : List QuerySource) (filter : Option Expr) (column : Expr) (name : String) (key : Expr)
    (collation : Collation) : Query :=
  { sources, filter, aggregate := true, groupBy := [(key, collation)],
    columns := [.scalar column], names := [name], orderBy := [], offset := 0, limit := none,
    limitParameter := none, offsetParameter := none, outer := 0, aggregates := [.countRows],
    having := some (.compare .gt none (.aggregateValue 0) (.literal (.integer 1)) .binary), distinct := none }

/-- The rows that a {lit}`WHERE` condition keeps: those for which it is true, or all rows when there is no condition. -/
def keptRows (context : EvalContext) (filter : Option Expr) (rows : List (List Value)) : List (List Value) :=
  rows.filter fun row => filter.all fun condition => truthy (condition.eval context row)

/-- Without a {lit}`WHERE` condition, every row is kept. Proof sketch: the filter keeps a row when the condition is absent. -/
theorem keptRows_none (context : EvalContext) (rows : List (List Value)) : keptRows context none rows = rows :=
  List.filter_eq_self.2 (by simp)

variable (sources : List QuerySource) (filter : Option Expr) (column : Expr) (name : String) (key : Expr)
  (collation : Collation)

/-- For every context, row and number, the condition {lit}`count(*) > 1`, with the number as the value of the
aggregate, is true exactly when the number is greater than one. Proof sketch: both operands are integers, and
integers compare by their order ({name}`Collation.compare_integer`). -/
theorem Expr.truthy_moreThanOne (context : EvalContext) (row : List Value) (n : Nat) :
    truthy ((Expr.compare .gt none (.aggregateValue 0) (.literal (.integer 1)) .binary).eval
      { context with aggregates := [.integer n] } row) = decide (1 < n) := by
  have aggregate : (Expr.aggregateValue 0).eval { context with aggregates := [.integer n] } row = .integer n := rfl
  have literal : ∀ c : EvalContext, (Expr.literal (.integer 1)).eval c row = .integer 1 := fun _ => rfl
  simp [Expr.eval_compare, comparisonOperands, Comparison.apply, aggregate, literal, Collation.compare_integer,
    Comparison.holds, truth]
  by_cases big : 1 < n
  · simp [Value.isNull, truthy, Int.compare_eq_gt.2 (by omega : (1 : Int) < n), big]
  · simp [Value.isNull, truthy, big]
    intro h
    have := Int.compare_eq_gt.1 h
    omega

/-- For every test on items, every way to make a result, and every function that agrees with "make a result when
the test holds, else none", the results of the function over a list are the results made from the items that pass
the test, in order. Proof sketch: induction on the list. -/
theorem filterMap_eq_map_filter_of {α β : Type} (keep : α → Bool) (make : α → β) (pick : α → Option β)
    (agrees : ∀ item, pick item = if keep item = true then some (make item) else none) :
    ∀ items : List α, items.filterMap pick = (items.filter keep).map make
  | [] => rfl
  | item :: rest => by
    by_cases kept : keep item = true <;>
      simp [agrees item, kept, filterMap_eq_map_filter_of keep make pick agrees rest]

/-- For every duplicate-key query, it is no compound, no {lit}`SELECT DISTINCT`, an aggregate query, without
{lit}`LIMIT`, with {lit}`count(*)` as its one aggregate and the one scalar column {lit}`column`. Proof sketch: each
field is the value that the definition of {name}`Query.duplicateKeys` gives. -/
theorem Query.duplicateKeys_shape :
    (Query.duplicateKeys sources filter column name key collation).compound = none ∧ (Query.duplicateKeys sources filter column name key collation).distinct = none ∧
    (Query.duplicateKeys sources filter column name key collation).aggregate = true ∧ (Query.duplicateKeys sources filter column name key collation).limit = none ∧
    (Query.duplicateKeys sources filter column name key collation).aggregates = [.countRows] ∧
    (Query.duplicateKeys sources filter column name key collation).columns = [.scalar column] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- For every duplicate-key query, the context of a group has the number of rows of the group as the value of its
one aggregate. Proof sketch: the definitions compute. -/
theorem Query.duplicateKeys_groupContext
    (context : EvalContext) (group : List (List Value)) :
    (Query.duplicateKeys sources filter column name key collation).groupContext context group =
      { context with aggregates := [.integer group.length] } := rfl

/-- For every duplicate-key query, the records over any rows are one record for each group of more than one row, of the
rows that {lit}`WHERE` keeps ({name}`keptRows`): the result column evaluated for the first row of the group and the
number of its rows as the value of the aggregate, without sort values. Proof sketch: the query is an aggregate query,
so each group of {name}`groups` is a record when {lit}`HAVING` is true for it; {name}`Expr.truthy_moreThanOne` gives its
value. -/
theorem Query.duplicateKeys_uniqueRecords (context : EvalContext) (rows : List (List Value)) :
    (Query.duplicateKeys sources filter column name key collation).uniqueRecords context rows =
      ((groups context [(key, collation)] (keptRows context filter rows)).filter fun group => decide (1 < group.length)).map
        fun group => ([column.eval { context with aggregates := [.integer group.length] } (group.headD [])], []) := by
  unfold Query.uniqueRecords records
  simp only [Query.duplicateKeys, queryGroups, filtered, keptRows, List.isEmpty_cons, Bool.false_eq_true, ite_true,
    ite_false, Query.groupContext]
  refine filterMap_eq_map_filter_of (fun (group : List (List Value)) => decide (1 < group.length))
    (fun group => ([column.eval { context with aggregates := [.integer group.length] } (group.headD [])], [])) _
    (fun group => ?_) _
  have counted : List.map (fun x => Aggregate.eval context group x) [Aggregate.countRows] = [.integer group.length] := rfl
  simp only [counted]
  have condition : Option.all (fun condition => truthy (Expr.eval { context with aggregates := [.integer group.length] }
      (group.headD []) condition)) (some (Expr.compare .gt none (.aggregateValue 0) (.literal (.integer 1)) .binary)) =
      decide (1 < group.length) := by
    rw [Option.all_some]
    exact Expr.truthy_moreThanOne context (group.headD []) group.length
  rw [condition]
  by_cases big : decide (1 < group.length) = true
  · simp [big]
  · simp [big]

/-- For every duplicate-key query, over any rows, the result rows are one row for each group of more than one row of the
rows that {lit}`WHERE` keeps ({name}`keptRows`): the result column evaluated for the first row of the group. Proof sketch:
a query without {lit}`ORDER BY` sorts nothing ({name}`stableSort_of_total`) and has no window, so the result is the
records of {name}`Query.duplicateKeys_uniqueRecords`. -/
theorem Query.duplicateKeys_results (context : EvalContext) (rows : List (List Value)) :
    (Query.duplicateKeys sources filter column name key collation).results context rows =
      ((groups context [(key, collation)] (keptRows context filter rows)).filter fun group => decide (1 < group.length)).map
        fun group => [column.eval { context with aggregates := [.integer group.length] } (group.headD [])] := by
  unfold Query.results
  dsimp only
  rw [stableSort_of_total _ (by simp [Query.duplicateKeys, compareSort]), Query.duplicateKeys_uniqueRecords]
  simp [Query.duplicateKeys, Function.comp_def]

/-- For every duplicate-key query, the window binds to the query itself, for any values. Proof sketch:
{name}`Query.bindWindow_literal`; the query has no window parameter. -/
theorem Query.duplicateKeys_bindWindow
    (parameters : List Value) :
    (Query.duplicateKeys sources filter column name key collation).bindWindow parameters = some (Query.duplicateKeys sources filter column name key collation) :=
  Query.bindWindow_literal parameters _ rfl rfl

/-- For every duplicate-key query whose expressions have no fallible call ({name}`Expr.isFallibleCall`), in a context
in which its expressions have no fault over the empty row and over each of the rows ({name}`Expr.evaluate`), the run
over those rows gives the one result ({name}`Query.duplicateKeys_results`), no fault, no overflow and no window
mismatch. Proof sketch: the window binds to the query ({name}`Query.duplicateKeys_bindWindow`); {lit}`count(*)` does not
overflow ({name}`Aggregate.fails`); there is no {lit}`DISTINCT`; and no expression has a fault, so the query neither
certainly nor possibly fails ({name}`Query.mustFail_of_faultless`, {name}`Query.mayFail_of_faultless`). -/
theorem Query.duplicateKeys_run_of_faultless
    (context : EvalContext)
    (plain : (Query.duplicateKeys sources filter column name key collation).expressions.all (!·.any Expr.isFallibleCall) = true)
    (rows : List (List Value))
    (faultless : ∀ row ∈ [] :: rows, ∀ expression ∈ (Query.duplicateKeys sources filter column name key collation).expressions,
      (expression.evaluate context row).2 = .none) :
    (Query.duplicateKeys sources filter column name key collation).run context rows =
      { rows := (Query.duplicateKeys sources filter column name key collation).results context rows, fault := .none, overflow := false,
        mismatch := false } := by
  unfold Query.run
  obtain ⟨compound, distinct, aggregate, limit, aggregates, columns⟩ := Query.duplicateKeys_shape sources filter column name key collation
  simp [compound, Query.duplicateKeys_bindWindow, Query.mustFail_of_faultless context _ rows faultless,
    Query.mayFail_of_faultless context _ rows plain faultless, Query.distinctCertain, distinct, Query.fails, aggregate,
    limit, aggregates, columns, Aggregate.fails]

/-- For every duplicate-key query, whose source rows in a context and database have no fault, and whose expressions
have no fallible call and no fault over the empty row and over each source row, the run as a subquery for the outer
row with no cells ({name}`Query.subqueryRun`) has the result rows of {name}`Query.duplicateKeys_results` as its rows,
no fault, and certain rows; it ends done. Proof sketch: as for {name}`Query.subqueryRun_simple`, with
{name}`Query.duplicateKeys_run_of_faultless`; a window of no {lit}`LIMIT` and no {lit}`OFFSET` cuts nowhere
({name}`certainCut`). -/
theorem Query.duplicateKeys_subqueryRun
    (context : EvalContext) (database : Database) (source : SourceRows)
    (found : (Query.duplicateKeys sources filter column name key collation).source context database = some source)
    (clean : source.fault = .none)
    (plain : (Query.duplicateKeys sources filter column name key collation).expressions.all (!·.any Expr.isFallibleCall) = true)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ (Query.duplicateKeys sources filter column name key collation).expressions,
      (expression.evaluate context row).2 = .none) :
    (Query.duplicateKeys sources filter column name key collation).subqueryRun context database [] =
      { rows := (Query.duplicateKeys sources filter column name key collation).results context source.rows, fault := .none,
        firstCertain := (Query.duplicateKeys sources filter column name key collation).windowCertain context source.rows (some 1),
        rowsCertain := true, ending := .done } := by
  have after : (Query.duplicateKeys sources filter column name key collation).sourceAfter context [] database = some source := by
    simpa [Query.sourceAfter, Query.source, Query.duplicateKeys] using found
  unfold Query.subqueryRun
  rw [after]
  simp only [Query.duplicateKeys_bindWindow sources filter column name key collation context.parameters,
    Query.duplicateKeys_run_of_faultless sources filter column name key collation context plain source.rows faultless, clean]
  simp [Fault.join, Fault.soften, Query.windowCertain, certainCut, Query.duplicateKeys]

end Belay.Sqlite.Model.Resolved
