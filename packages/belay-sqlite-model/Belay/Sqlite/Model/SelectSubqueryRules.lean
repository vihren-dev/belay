import Belay.Sqlite.Model.SelectCalmRule
import Belay.Sqlite.Model.SelectProjectionRules
import Belay.Sqlite.Model.ExprContextLaws

set_option doc.verso true

/-! Subquery rules of a SELECT (ADR 0027, D1, phase {lit}`subquery`): the run of each subquery of
a calm statement, for each outer row, in the statement context; the run of a subquery that is no
compound and runs without fault; and the emptiness of its rows, which {lit}`EXISTS` reads. A
correlated subquery runs once for each outer row, so each rule takes the outer row as an
argument: a proof for one outer row does not serve another. -/

namespace Belay.Sqlite.Model

namespace Resolved

/-- Statement subquery rule: for every values, database, subqueries, index of a subquery
{lit}`inner` in the list and outer row, the run of subquery {lit}`index` in the statement context
({name}`EvalContext.statement`) is the run of {lit}`inner` for the outer row
({name}`Query.subqueryRun`) in the subquery context one depth below the length of the list
({name}`subqueryContext`). Proof sketch: the list is not empty, so the depth of the statement
context is a successor, and {name}`subqueryContext` at a successor runs the subquery at its index. -/
theorem EvalContext.statement_subqueries (parameters : List Value) (database : Database) {subqueries : List Query}
    {index : Nat} {inner : Query} (found : subqueries[index]? = some inner) (outer : List Value) :
    (EvalContext.statement parameters database subqueries).subqueries index outer =
      inner.subqueryRun (subqueryContext 0 {} parameters database subqueries none (subqueries.length - 1)) database
        outer := by
  have inside := (List.getElem?_eq_some_iff.mp found).1
  obtain ⟨depth, length⟩ : ∃ depth, subqueries.length = depth + 1 := ⟨subqueries.length - 1, by omega⟩
  simp only [EvalContext.statement, statementContext, length, subqueryContext, found, Nat.add_sub_cancel]

/-- One-subquery rule: for every values, database, subquery {lit}`inner` and outer row, the run of
subquery 0 in the statement context of the one subquery is the run of {lit}`inner` for the outer row
in the context of the values ({name}`EvalContext.bound`). Proof sketch: the statement context has
depth one, and depth 0 is the context of the values. -/
theorem EvalContext.statement_one (parameters : List Value) (database : Database) (inner : Query)
    (outer : List Value) :
    (EvalContext.statement parameters database [inner]).subqueries 0 outer =
      inner.subqueryRun (EvalContext.bound parameters) database outer := rfl

/-- One-subquery context rule: for every values, database, subquery {lit}`inner` and expression, the
expression has the same value and fault over the row with no cells in the statement context of the
one subquery as in the context of the values with the run of {lit}`inner` for that row
({name}`EvalContext.withRuns`). Proof sketch: the two contexts differ only in their subqueries,
which agree at the row with no cells ({name}`EvalContext.statement_one`), so
{name}`Expr.evaluate_withSubqueries` applies. -/
theorem Expr.evaluate_statement_one (parameters : List Value) (database : Database) (inner : Query)
    (expression : Expr) :
    expression.evaluate (EvalContext.statement parameters database [inner]) [] =
      expression.evaluate ((EvalContext.bound parameters).withRuns
        [inner.subqueryRun (EvalContext.bound parameters) database []]) [] := by
  refine ((Expr.evaluate_withSubqueries (EvalContext.statement parameters database [inner]) []
    (fun index _ => ([inner.subqueryRun (EvalContext.bound parameters) database []][index]?).getD
      { rows := [], fault := .none }) (fun index => ?_) expression).1).symm
  cases index with
  | zero => rfl
  | succ later => simp [statementContext, subqueryContext]

/-- Subquery run rule: for every context, database, outer row, optional initial database, query
that is no compound, source rows {lit}`source` of the query after the outer row
({name}`Query.sourceAfter`) without fault, and query {lit}`bound` that the window binds to with the
values of the context: when {lit}`bound` over the source rows has no failing aggregate
({name}`Query.fails`), does not certainly or possibly fail ({name}`Query.mustFail`,
{name}`Query.mayFail`) and keeps the same rows for {lit}`DISTINCT` in every order
({name}`Query.distinctCertain`), the run of the query as a subquery for the outer row
({name}`Query.subqueryRun`) has

* the result rows of {lit}`bound` over the source rows,
* no fault,
* the certainty of its window of at most one row, of its window, and of its window over complete
  rows ({name}`Query.windowCertain`), and
* the end {lean}`RunEnd.done`.

Proof sketch: {lit}`bound` has no window parameter and is no compound
({name}`Query.bindWindow_some`), so {name}`Query.run_single` gives its run, whose fault is {lean}`Fault.none`. -/
theorem Query.subqueryRun_clean (context : EvalContext) (database : Database) (outer : List Value)
    (initial : Option Database) {query bound : Query} {source : SourceRows} (single : query.compound = none)
    (found : query.sourceAfter context outer database initial = some source) (clean : source.fault = .none)
    (window : query.bindWindow context.parameters = some bound)
    (noOverflow : bound.fails context source.rows = false) (noMustFail : bound.mustFail context source.rows = false)
    (noMayFail : bound.mayFail context source.rows = false)
    (distinct : bound.distinctCertain context source.rows = true) :
    query.subqueryRun context database outer initial =
      { rows := bound.results context source.rows, fault := .none,
        firstCertain := bound.windowCertain context source.rows (some (min 1 (bound.limit.getD 1))),
        rowsCertain := bound.windowCertain context source.rows bound.limit,
        sourceCertain := bound.windowCertain context source.rows bound.limit true, ending := .done } := by
  obtain ⟨limit, offset, shape⟩ := Query.bindWindow_some _ query bound window
  have boundSingle : bound.compound = none := by rw [shape]; exact single
  have boundWindow : bound.bindWindow context.parameters = some bound :=
    Query.bindWindow_literal _ bound (by rw [shape]) (by rw [shape])
  unfold Query.subqueryRun
  rw [found]
  simp only [window, Query.run_single context bound source.rows boundSingle boundWindow, noOverflow, noMustFail,
    noMayFail, distinct, clean]
  simp [Fault.join, Fault.soften]

/-- Faultless subquery rule: {name}`Query.subqueryRun_clean` for a query without a window
parameter and without a fallible call, whose expressions have no fault over the empty row and
over each source row: for every context, database, outer row and optional initial database, under
the premises on the source rows, the overflow and {lit}`DISTINCT`, the run of the query as a
subquery for the outer row has the result rows of the query over the source rows, no fault, and
ends done, with the certainty flags of {name}`Query.subqueryRun_clean` for the query itself.
Proof sketch: the window binds to the query ({name}`Query.bindWindow_literal`), and expressions
without a fault give no failure ({name}`Query.mustFail_of_faultless`,
{name}`Query.mayFail_of_faultless`). -/
theorem Query.subqueryRun_of_faultless (context : EvalContext) (database : Database) (outer : List Value)
    (initial : Option Database) {query : Query} {source : SourceRows} (single : query.compound = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (found : query.sourceAfter context outer database initial = some source) (clean : source.fault = .none)
    (plain : query.expressions.all (!·.any Expr.isFallibleCall) = true)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate context row).2 = .none)
    (noOverflow : query.fails context source.rows = false)
    (distinct : query.distinctCertain context source.rows = true) :
    query.subqueryRun context database outer initial =
      { rows := query.results context source.rows, fault := .none,
        firstCertain := query.windowCertain context source.rows (some (min 1 (query.limit.getD 1))),
        rowsCertain := query.windowCertain context source.rows query.limit,
        sourceCertain := query.windowCertain context source.rows query.limit true, ending := .done } :=
  Query.subqueryRun_clean context database outer initial single found clean
    (Query.bindWindow_literal context.parameters query limitParameter offsetParameter) noOverflow
    (Query.mustFail_of_faultless context query source.rows faultless)
    (Query.mayFail_of_faultless context query source.rows plain faultless) distinct

/-- Emptiness rule: for every context, query that is no compound and has no {lit}`DISTINCT`, no
aggregation, no {lit}`OFFSET` and no {lit}`LIMIT 0`, and rows, the query has no result rows
({name}`Query.results`) exactly when {lit}`WHERE` keeps no row ({name}`filtered`). This is what
{lit}`EXISTS` reads of a subquery. Proof sketch: sorting keeps the records as a permutation, a
window that starts at the first record and keeps at least one keeps a record when there is one,
and the records are one for each kept row ({name}`Query.uniqueRecords_outputs_plain`). -/
theorem Query.results_eq_nil_iff_plain (context : EvalContext) {query : Query} (single : query.compound = none)
    (noDistinct : query.distinct = none) (plain : query.aggregate = false) (noOffset : query.offset = 0)
    (limited : query.limit ≠ some 0) (rows : List (List Value)) :
    query.results context rows = [] ↔ filtered context query rows = [] := by
  have outputs := congrArg List.length (query.uniqueRecords_outputs_plain context single noDistinct plain rows)
  simp only [List.length_map] at outputs
  have sorted := (stableSort_perm (fun a b => (compareSort (query.orderBy.map fun term => (term.descending,
    term.collation)) a.2 b.2).isLE) (query.uniqueRecords context rows)).length_eq
  rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff (l := filtered context query rows), ← outputs, ← sorted]
  unfold Query.results
  simp only [noOffset, List.drop_zero, List.length_map]
  split
  · next limit same => cases limit with
    | zero => exact absurd same limited
    | succ => simp [List.length_take]
  · rfl

/-- Unordered result rule: for every context, query that is no compound and has no
{lit}`DISTINCT`, no aggregation, no {lit}`ORDER BY`, no {lit}`OFFSET` and no {lit}`LIMIT`, and
rows, the result rows of the query ({name}`Query.results`) are the result rows
({name}`Query.rowOutput`) of the rows that {lit}`WHERE` keeps ({name}`filtered`), in order. A
subquery that {lit}`IN` or a scalar subquery reads has this order in the model. Proof sketch:
without sort terms every two records are in order, so the sort keeps them
({name}`stableSort_of_total`), and {name}`Query.uniqueRecords_outputs_plain` gives the records. -/
theorem Query.results_plain_unordered (context : EvalContext) {query : Query} (single : query.compound = none)
    (noDistinct : query.distinct = none) (plain : query.aggregate = false) (unordered : query.orderBy = [])
    (noOffset : query.offset = 0) (noLimit : query.limit = none) (rows : List (List Value)) :
    query.results context rows = (filtered context query rows).map (query.rowOutput context) := by
  unfold Query.results
  simp only [unordered, List.map_nil, noOffset, noLimit, List.drop_zero]
  rw [stableSort_of_total _ (by simp [compareSort])]
  exact query.uniqueRecords_outputs_plain context single noDistinct plain rows

/-- Short window rule: for every context, query without {lit}`OFFSET`, rows with at most one record
({name}`Query.uniqueRecords`), limit and choice of complete rows, the first values of the window are
certain ({name}`Query.windowCertain`): no cut falls between two records. A scalar subquery whose
{lit}`WHERE` keeps at most one row reads a certain value. Proof sketch: the cut at the start is
certain, and the sorted records have no second record ({name}`certainCut`). -/
theorem Query.windowCertain_of_short (context : EvalContext) {query : Query} {rows : List (List Value)}
    (noOffset : query.offset = 0) (short : (query.uniqueRecords context rows).length ≤ 1) (limit : Option Nat)
    (wholeRows : Bool) : query.windowCertain context rows limit wholeRows = true := by
  have sortedShort : (stableSort (fun a b => (compareSort (query.orderBy.map fun term => (term.descending,
      term.collation)) a.2 b.2).isLE) (query.uniqueRecords context rows)).length ≤ 1 := by
    rw [(stableSort_perm _ _).length_eq]; exact short
  unfold Query.windowCertain
  cases limit with
  | none => simp [noOffset, certainCut]
  | some count =>
    cases count with
    | zero => simp
    | succ count =>
      have past := List.getElem?_eq_none (Nat.le_trans sortedShort (Nat.succ_le_succ (Nat.zero_le count)))
      simp only [noOffset, Option.all_some, Nat.zero_add]
      simp [certainCut, past]

end Resolved

end Belay.Sqlite.Model
