import Belay.Sqlite.Model.SelectOrderRules

set_option doc.verso true

/-! The rules of the {lit}`order` and {lit}`window` phases of a query that depend on its window
({lit}`OFFSET` and {lit}`LIMIT`): without a window, a result is all the query's records in order; with
a window, the result has the length that the window takes; and the order rule in a form that applies
only to a query with a window, so that a procedure that applies every matching rule does not also give
the weaker fact for a query without one. -/

namespace Belay.Sqlite.Model.Resolved

/-- Order rule without a window: for every context, query with {lit}`OFFSET` 0 and no
{lit}`LIMIT`, rows and result that the model permits, the result is the rows of a permutation of
all the query's records ({name}`Query.uniqueRecords`) in order by the {lit}`ORDER BY` terms
({name}`compareSort`). Proof sketch: {name}`Query.exists_sorted_of_mem_possibleResults`; the
result has as many rows as the records ({name}`Query.perm_of_mem_possibleResults`), and a sublist
as long as its list is the list. -/
theorem Query.exists_sorted_perm_of_mem_possibleResults {context : EvalContext} {query : Query}
    {rows result : List (List Value)} (offset : query.offset = 0) (limit : query.limit = none)
    (member : result ∈ query.possibleResults context rows) :
    ∃ ordered : List Record, ordered.Perm (query.uniqueRecords context rows) ∧
      ordered.Pairwise (fun a b =>
        (compareSort (query.orderBy.map fun term => (term.descending, term.collation)) a.2 b.2).isLE) ∧
      result = ordered.map Prod.fst := by
  obtain ⟨ordered, ⟨picked, sublist, perm⟩, sorted, rfl⟩ := Query.exists_sorted_of_mem_possibleResults member
  have length := (Query.perm_of_mem_possibleResults offset limit member).length_eq
  simp only [List.length_map] at length
  rw [sublist.eq_of_length (by rw [← perm.length_eq, length])] at perm
  exact ⟨ordered, perm, sorted, rfl⟩

/-- Window rule: for every context, query, rows and result that the model permits, the result has
as many rows as the window takes of the query's records ({name}`Query.uniqueRecords`):
- without {lit}`LIMIT`, the number of records after {lit}`OFFSET`, 0 when the offset is past the end;
- with {lit}`LIMIT` {lit}`limit`, the smaller of {lit}`limit` and that number.

Proof sketch: every result has as many rows as {name}`Query.results`
({name}`Query.possibleResults_length`), which is the window over the sorted records, a permutation
of the records. -/
theorem Query.length_of_mem_possibleResults {context : EvalContext} {query : Query}
    {rows result : List (List Value)} (member : result ∈ query.possibleResults context rows) :
    (query.limit = none → result.length = (query.uniqueRecords context rows).length - query.offset) ∧
      ∀ limit, query.limit = some limit →
        result.length = min limit ((query.uniqueRecords context rows).length - query.offset) := by
  have sorted : (query.sortedRecords context rows).length = (query.uniqueRecords context rows).length :=
    (stableSort_perm _ _).length_eq
  rw [Query.possibleResults_length context query rows result member, Query.results_window]
  refine ⟨fun none => ?_, fun limit some => ?_⟩
  · simp [Query.stop, none, windowRows, sorted]
  · simp [Query.stop, some, windowRows, sorted]

/-- Window order rule: for every context, query with an {lit}`OFFSET` other than 0 or a {lit}`LIMIT`,
rows and result that the model permits for the query over the rows, the result is the rows of a
permutation of a sublist of the records in order by the {lit}`ORDER BY` terms, as
{name}`Query.exists_sorted_of_mem_possibleResults` says. The premise on the window only routes the
rule: without a window, {name}`Query.exists_sorted_perm_of_mem_possibleResults` gives all the records,
which is more. Proof sketch: {name}`Query.exists_sorted_of_mem_possibleResults`, which does not use
the premise. -/
theorem Query.exists_sorted_of_mem_possibleResults_window {context : EvalContext} {query : Query}
    {rows result : List (List Value)} (_window : query.offset ≠ 0 ∨ query.limit ≠ none)
    (member : result ∈ query.possibleResults context rows) :
    ∃ ordered : List Record,
      (∃ picked : List Record, picked.Sublist (query.uniqueRecords context rows) ∧ ordered.Perm picked) ∧
        ordered.Pairwise (fun a b =>
          (compareSort (query.orderBy.map fun term => (term.descending, term.collation)) a.2 b.2).isLE) ∧
        result = ordered.map Prod.fst :=
  Query.exists_sorted_of_mem_possibleResults member

end Belay.Sqlite.Model.Resolved
