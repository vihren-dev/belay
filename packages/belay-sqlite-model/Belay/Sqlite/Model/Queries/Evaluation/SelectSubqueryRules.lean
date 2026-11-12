import Belay.Sqlite.Model.Queries.Evaluation.SelectCalmRule
import Belay.Sqlite.Model.Queries.Evaluation.SelectProjectionRules
import Belay.Sqlite.Model.Queries.Evaluation.ExprContextLaws
import Belay.Sqlite.Model.Queries.Evaluation.Subqueries

set_option doc.verso true

namespace Belay.Sqlite.Model

namespace Resolved

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

/-- Unordered result rule: for every context, query that is no compound and has no {lit}`DISTINCT`,
no {lit}`ORDER BY`, no {lit}`OFFSET` and no {lit}`LIMIT`, and rows, the result rows of the query
({name}`Query.results`) are the rows of its records ({name}`records`) over the rows that {lit}`WHERE` keeps
({name}`filtered`), in order, with or without aggregation. Proof sketch: without sort terms the sort keeps the
records ({name}`stableSort_of_total`). -/
theorem Query.results_unordered (context : EvalContext) {query : Query} (single : query.compound = none)
    (noDistinct : query.distinct = none) (unordered : query.orderBy = []) (noOffset : query.offset = 0)
    (noLimit : query.limit = none) (rows : List (List Value)) :
    query.results context rows = (records context query (filtered context query rows)).map Prod.fst := by
  unfold Query.results
  simp only [unordered, List.map_nil, noOffset, noLimit, List.drop_zero]
  rw [stableSort_of_total _ (by simp [compareSort])]
  simp only [Query.uniqueRecords, single, noDistinct]

/-- Unordered plain result rule: for every context, query that is no compound and has no
{lit}`DISTINCT`, no aggregation, no {lit}`ORDER BY`, no {lit}`OFFSET` and no {lit}`LIMIT`, and
rows, the result rows of the query ({name}`Query.results`) are the result rows
({name}`Query.rowOutput`) of the rows that {lit}`WHERE` keeps ({name}`filtered`), in order. A subquery that
{lit}`IN` or a scalar subquery reads has this order. Proof sketch: {name}`Query.results_unordered`. -/
theorem Query.results_plain_unordered (context : EvalContext) {query : Query} (single : query.compound = none)
    (noDistinct : query.distinct = none) (plain : query.aggregate = false) (unordered : query.orderBy = [])
    (noOffset : query.offset = 0) (noLimit : query.limit = none) (rows : List (List Value)) :
    query.results context rows = (filtered context query rows).map (query.rowOutput context) := by
  rw [query.results_unordered context single noDistinct unordered noOffset noLimit]
  exact records_outputs_plain context plain _

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
