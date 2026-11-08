import Belay.Sqlite.Model.SelectWindowRules
import Belay.Sqlite.Model.QueryPlainLaws
import Belay.Sqlite.Model.Subqueries

set_option doc.verso true

/-! The plain query value and the rules of a query without {lit}`ORDER BY` and window (ADR 0027,
D1). {lit}`Query.simple` builds the query of a read without aggregation, grouping, ordering,
window, {lit}`HAVING`, {lit}`DISTINCT` or compound. The rules hold for every query with the
named fields: a query without a sort term has one tie group, so the model permits one result,
and a window without {lit}`OFFSET` and {lit}`LIMIT` cuts nowhere. -/

namespace Belay.Sqlite.Model.Resolved

/-- The plain query of the given sources, {lit}`WHERE` condition and result columns with their
names: it is not an aggregate query, and has no grouping, ordering, window, {lit}`HAVING`,
{lit}`DISTINCT` or compound, and it reads no cell of an outer query. For example, the query of
{lit}`SELECT 1 FROM t WHERE p` is {lit}`Query.simple [QuerySource.first 0] (some p) [.scalar 1] ["1"]`. -/
def Query.simple (sources : List QuerySource) (filter : Option Expr) (columns : List Output) (names : List String) :
    Query :=
  { sources, filter, aggregate := false, groupBy := [], columns, names, orderBy := [], offset := 0, limit := none,
    limitParameter := none, offsetParameter := none, outer := 0, aggregates := [], having := none, distinct := none }

/-- The query {lit}`SELECT 1 WHERE c` of a resolved condition {lit}`c`: it has no source, the one result
column {lit}`1` named {lit}`"1"`, and no other clause. -/
abbrev Query.selectOneWhere (condition : Expr) : Query :=
  Query.simple [] (some condition) [.scalar (.literal (.integer 1))] ["1"]

/-- The expressions of {lit}`SELECT 1 WHERE c` are the condition and the literal 1. Proof sketch: the
definitions compute. -/
theorem Query.selectOneWhere_expressions (condition : Expr) :
    (Query.selectOneWhere condition).expressions = [condition, .literal (.integer 1)] := rfl

/-- For every context and condition whose evaluation over the row with no cells has no fault, every
expression of {lit}`SELECT 1 WHERE c` has none: the condition, and the literal 1. Proof sketch:
{name}`Query.selectOneWhere_expressions`; a literal has no fault. -/
theorem Query.selectOneWhere_faultless (context : EvalContext) (condition : Expr)
    (none : (condition.evaluate context []).2 = .none) :
    ∀ expression ∈ (Query.selectOneWhere condition).expressions, (expression.evaluate context []).2 = .none := by
  intro expression member
  rw [Query.selectOneWhere_expressions] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact none
  · simp only [List.mem_singleton] at member
    subst member
    rfl

/-- Outer source rule: for every context, database, optional initial database and query that
reads no cell of an outer query, the source rows after the empty outer row
({name}`Query.sourceAfter`) are the source rows of the query ({name}`Query.source`). Proof sketch:
both fold the sources over the one row with no cells. -/
theorem Query.sourceAfter_of_outer_zero (context : EvalContext) (database : Database) (initial : Option Database)
    {query : Query} (outer : query.outer = 0) :
    query.sourceAfter context [] database initial = query.source context database initial := by
  simp [Query.sourceAfter, outer, Query.source]

/-- Whole window rule: for every context, query without {lit}`OFFSET`, rows and choice of complete
rows, the window without {lit}`LIMIT` is certain ({name}`Query.windowCertain`): it cuts nowhere.
Proof sketch: the cut at the start is certain ({name}`certainCut`), and no limit adds a cut. -/
theorem Query.windowCertain_whole (context : EvalContext) {query : Query} (noOffset : query.offset = 0)
    (rows : List (List Value)) (wholeRows : Bool) : query.windowCertain context rows none wholeRows = true := by
  simp [Query.windowCertain, noOffset, certainCut]

/-- For every nonempty list of records, the tie groups without {lit}`ORDER BY` terms are the records
as one group. Proof sketch: induction on the records; each record is equal to the first record of the
group after it, because no term separates them. -/
theorem tieGroups_nil_directions : ∀ records : List Record, records ≠ [] → tieGroups [] records = [records]
  | [], h => absurd rfl h
  | [record], _ => by simp [tieGroups]
  | record :: next :: more, _ => by
    have rest := tieGroups_nil_directions (next :: more) (List.cons_ne_nil _ _)
    rw [tieGroups, rest]
    simp [compareSort]

/-- Unordered result rule: for every context, query without {lit}`ORDER BY`, {lit}`OFFSET` and
{lit}`LIMIT`, and rows, the only result that the model permits ({name}`Query.possibleResults`) is
the normal form of its result rows ({name}`Query.results`). The query may aggregate, group or have
{lit}`DISTINCT`. Proof sketch: no term orders the records, so the sort keeps them
({name}`stableSort_of_total`) and they are one tie group ({name}`tieGroups_nil_directions`); the
window takes the whole group, which is its one choice. -/
theorem Query.possibleResults_unordered (context : EvalContext) {query : Query} (unordered : query.orderBy = [])
    (noOffset : query.offset = 0) (noLimit : query.limit = none) (rows : List (List Value)) :
    query.possibleResults context rows = [normalForm (query.results context rows)] := by
  have sorted : query.sortedRecords context rows = query.uniqueRecords context rows := by
    unfold Query.sortedRecords
    exact stableSort_of_total _ (by simp [unordered, compareSort]) _
  have results : query.results context rows = (query.uniqueRecords context rows).map Prod.fst := by
    rw [Query.results_window]
    simp [noOffset, Query.stop, noLimit, windowRows, sorted]
  unfold Query.possibleResults Query.tieGroupRows
  rw [sorted]
  simp only [unordered, List.map_nil]
  by_cases empty : query.uniqueRecords context rows = []
  · simp [empty, results, tieGroups, windowChoices, choiceResults, distinctLists, normalForm, stableSort]
  · rw [tieGroups_nil_directions _ empty]
    simp [results, windowChoices, noOffset, Query.stop, noLimit, groupChoices, groupSlice, windowRows,
      choiceResults, distinctLists]

end Belay.Sqlite.Model.Resolved
