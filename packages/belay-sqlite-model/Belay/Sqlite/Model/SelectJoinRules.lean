import Belay.Sqlite.Model.QueryJoinLaws

set_option doc.verso true

/-! Join rules of a SELECT (ADR 0027, D1, phase {lit}`source`): the complete rows of each join
kind as a collection, with their order and multiplicity. An inner join gives, for each left row in
order, the left row followed by each matching candidate in candidate order; a left join puts one
row with NULL cells in place of a left row without a match; a right join adds each candidate that
no left row matches after NULL cells, which keep the enclosing query's cells; a full join does both.
The cardinality rule counts the matches of each left row. -/

namespace Belay.Sqlite.Model.Resolved

/-- The rows of a join for one left row as a filter: the left row followed by each candidate for
which the {lit}`ON` condition is true, in candidate order. -/
def matchedRows (context : EvalContext) (join : QuerySource) (candidates : List (List Value)) (row : List Value) :
    List (List Value) :=
  (candidates.filter fun cells => join.matches context (row ++ cells)).map (row ++ ·)

/-- Match rule: for every context, left row, join and candidate rows, {name}`joinMatches` gives
exactly {name}`matchedRows`: each matching candidate once for each time it occurs, in candidate
order. Proof sketch: induction on the candidates. -/
theorem joinMatches_eq (context : EvalContext) (row : List Value) (join : QuerySource) :
    ∀ candidates : List (List Value), joinMatches context row join candidates = matchedRows context join candidates row
  | [] => rfl
  | cells :: rest => by
    have later := joinMatches_eq context row join rest
    unfold matchedRows at later ⊢
    unfold joinMatches at later ⊢
    by_cases matched : join.matches context (row ++ cells) = true <;> simp_all

/-- For every context, join, candidate rows and left row, the left row has no match
({name}`matchedRows` is empty) exactly when the condition is false for every candidate. Proof sketch:
the map of a filter is empty exactly when the filter keeps nothing. -/
theorem matchedRows_eq_nil (context : EvalContext) (join : QuerySource) (candidates : List (List Value))
    (row : List Value) :
    matchedRows context join candidates row = [] ↔ ∀ cells ∈ candidates, join.matches context (row ++ cells) = false := by
  simp [matchedRows, List.filter_eq_nil_iff]

/-- The rows of a left join for one left row: its {name}`matchedRows`, or, without a match, the
left row followed by one NULL for each of the {lit}`columns` columns of the source. -/
def paddedRows (context : EvalContext) (join : QuerySource) (columns : Nat) (candidates : List (List Value))
    (row : List Value) : List (List Value) :=
  if (matchedRows context join candidates row).isEmpty then [row ++ List.replicate columns .null]
  else matchedRows context join candidates row

/-- For every context, inner or right join, source width and candidate rows, the rows of
{name}`joinRow` for a left row are its {name}`matchedRows`. Proof sketch: such a join gives
{name}`joinMatches`, which {name}`joinMatches_eq` rewrites. -/
theorem joinRow_matched (context : EvalContext) {join : QuerySource} (kind : join.kind = .inner ∨ join.kind = .right)
    (columns : Nat) (candidates : List (List Value)) :
    joinRow context join columns candidates = matchedRows context join candidates := by
  funext row
  rcases kind with kind | kind <;> simp [joinRow, kind, joinMatches_eq]

/-- For every context, left or full join, source width and candidate rows, the rows of
{name}`joinRow` for a left row are its {name}`paddedRows`. Proof sketch: both test whether the
matches are empty; {name}`joinMatches_eq` rewrites the matches. -/
theorem joinRow_padded (context : EvalContext) {join : QuerySource} (kind : join.kind = .left ∨ join.kind = .full)
    (columns : Nat) (candidates : List (List Value)) :
    joinRow context join columns candidates = paddedRows context join columns candidates := by
  funext row
  rcases kind with kind | kind <;> simp [joinRow, kind, joinMatches_eq, paddedRows]

/-- Inner join rule: for every context, inner join, left width, left rows, source width, candidate
rows and enclosing cells, the joined rows are the {name}`matchedRows` of each left row, in left
order. Proof sketch: an inner join adds no unmatched row, and {name}`joinRow_matched` gives the rows
of each left row. -/
theorem joinRows_inner (context : EvalContext) {join : QuerySource} (inner : join.kind = .inner) (width : Nat)
    (left : List (List Value)) (columns : Nat) (candidates : List (List Value)) (outer : List Value) :
    joinRows context width left join columns candidates outer = left.flatMap (matchedRows context join candidates) := by
  simp [joinRows, inner, joinRow_matched context (.inl inner)]

/-- Left join rule: for every context, left join, left width, left rows, source width, candidate
rows and enclosing cells, the joined rows are the {name}`paddedRows` of each left row, in left
order: each left row is kept, with NULL source cells when no candidate matches it. Proof sketch: a
left join adds no unmatched row, and {name}`joinRow_padded` gives the rows of each left row. -/
theorem joinRows_left (context : EvalContext) {join : QuerySource} (kind : join.kind = .left) (width : Nat)
    (left : List (List Value)) (columns : Nat) (candidates : List (List Value)) (outer : List Value) :
    joinRows context width left join columns candidates outer = left.flatMap (paddedRows context join columns candidates) := by
  simp [joinRows, kind, joinRow_padded context (.inl kind)]

/-- The rows that a right or full join adds: each candidate that no left row matches
({name}`unmatchedRight`), in candidate order, after the enclosing query's cells {lit}`outer` and
NULL in the other cells of the left width. -/
def unmatchedRows (context : EvalContext) (join : QuerySource) (width : Nat) (left candidates : List (List Value))
    (outer : List Value) : List (List Value) :=
  (unmatchedRight context left join candidates).map ((outer ++ List.replicate (width - outer.length) .null) ++ ·)

/-- Right join rule: for every context, right join, left width, left rows, source width, candidate
rows and enclosing cells, the joined rows are the {name}`matchedRows` of each left row, in left
order, then the {name}`unmatchedRows`: each candidate is kept, with NULL left cells when no left row
matches it. Proof sketch: {name}`joinRow_matched` gives the rows of each left row. -/
theorem joinRows_right (context : EvalContext) {join : QuerySource} (kind : join.kind = .right) (width : Nat)
    (left : List (List Value)) (columns : Nat) (candidates : List (List Value)) (outer : List Value) :
    joinRows context width left join columns candidates outer =
      left.flatMap (matchedRows context join candidates) ++ unmatchedRows context join width left candidates outer := by
  simp [joinRows, kind, joinRow_matched context (.inr kind), unmatchedRows]

/-- Full join rule: for every context, full join, left width, left rows, source width, candidate
rows and enclosing cells, the joined rows are the {name}`paddedRows` of each left row, in left
order, then the {name}`unmatchedRows`. Proof sketch: {name}`joinRow_padded` gives the rows of each
left row. -/
theorem joinRows_full (context : EvalContext) {join : QuerySource} (kind : join.kind = .full) (width : Nat)
    (left : List (List Value)) (columns : Nat) (candidates : List (List Value)) (outer : List Value) :
    joinRows context width left join columns candidates outer =
      left.flatMap (paddedRows context join columns candidates) ++ unmatchedRows context join width left candidates outer := by
  simp [joinRows, kind, joinRow_padded context (.inr kind), unmatchedRows]

/-- Inner join cardinality rule: for every context, inner join, widths, left rows, candidate rows
and enclosing cells, the number of joined rows is the sum, over the left rows, of the number of
candidates that match the left row. Proof sketch: {name}`joinRows_inner`; each left row gives one
row for each matching candidate. -/
theorem joinRows_inner_length (context : EvalContext) {join : QuerySource} (inner : join.kind = .inner) (width : Nat)
    (left : List (List Value)) (columns : Nat) (candidates : List (List Value)) (outer : List Value) :
    (joinRows context width left join columns candidates outer).length =
      (left.map fun row => candidates.countP fun cells => join.matches context (row ++ cells)).sum := by
  rw [joinRows_inner context inner]
  simp [matchedRows, List.length_flatMap, List.countP_eq_length_filter]

/-- Unique match rule: for every context, inner join, widths, left rows, candidate rows and
enclosing cells, when exactly one candidate matches each left row, the join has as many rows as the
left rows. Proof sketch: {name}`joinRows_inner_length` with a sum of ones. -/
theorem joinRows_inner_length_of_unique (context : EvalContext) {join : QuerySource} (inner : join.kind = .inner)
    (width : Nat) {left : List (List Value)} (columns : Nat) {candidates : List (List Value)} (outer : List Value)
    (unique : ∀ row ∈ left, (candidates.countP fun cells => join.matches context (row ++ cells)) = 1) :
    (joinRows context width left join columns candidates outer).length = left.length := by
  rw [joinRows_inner_length context inner, List.map_congr_left unique (g := fun _ => 1)]
  clear unique
  induction left with
  | nil => rfl
  | cons _ _ later => simp [later, Nat.add_comm]

/-- Two-table source rule: for every context, query whose sources are the table at one position
as the first source and then a join of the table at another position, and database with both
tables, the source rows of the query are the rows of the join ({name}`joinRows`) of the scans of
the two tables ({name}`sourceRows`), with the sum of their widths and no fault. Proof sketch: the
fold joins the first table to the one row without cells, which keeps its rows, then the second. -/
theorem Query.source_two_tables (context : EvalContext) (query : Query) (database : Database)
    {firstPosition secondPosition : Nat} {join : QuerySource} {first second : Table}
    (sources : query.sources = [QuerySource.first firstPosition, join]) (isTable : join.source = .table secondPosition)
    (firstPresent : database.table firstPosition = some first) (secondPresent : database.table secondPosition = some second) :
    query.source context database = some
      { rows := joinRows context first.shape.columns.length (sourceRows first) join second.shape.columns.length
          (sourceRows second) [],
        width := first.shape.columns.length + second.shape.columns.length, fault := .none } := by
  simp [Query.source, sources, List.foldlM, QuerySource.join, QuerySource.first, QuerySource.joinTable, joinRows,
    joinRow, joinMatches, QuerySource.matches, bind, Option.bind, pure, firstPresent, secondPresent, isTable]

end Belay.Sqlite.Model.Resolved
