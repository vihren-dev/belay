import Belay.Sqlite.Model.Queries.Evaluation.PlainQueryRules

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- The shape of the compound subquery {lit}`q1 EXCEPT q2`: it has no source and no expression, no ordering and no
window, no cell of an outer query, and the compound of the term {lit}`first` and the one operator {lit}`EXCEPT` with the term
{lit}`later`, under the collations. -/
structure Query.PlainExcept (query : Query) (first later : Nat) (collations : List Collation) : Prop where
  /-- The query has no source. -/
  sources : query.sources = []
  /-- The query reads no cell of an outer query. -/
  outer : query.outer = 0
  /-- The query has no {lit}`ORDER BY`. -/
  orderBy : query.orderBy = []
  /-- The query skips no row. -/
  offset : query.offset = 0
  /-- The query has no {lit}`LIMIT`. -/
  limit : query.limit = none
  /-- The query has no {lit}`LIMIT ?`. -/
  limitParameter : query.limitParameter = none
  /-- The query has no {lit}`OFFSET ?`. -/
  offsetParameter : query.offsetParameter = none
  /-- The query has no expression of its own: the expressions are those of the terms. -/
  expressions : query.expressions = []
  /-- The query is the compound of the two terms. -/
  compound : query.compound = some { first, rest := [(.except, later)], collations }

/-- For every query of the shape {name}`Query.PlainExcept` and every context, the one result over the one row with
no cells is {lit}`EXCEPT` of the rows of the two terms ({name}`CompoundOperator.combine`). Proof sketch: no
{lit}`ORDER BY` sorts nothing ({name}`stableSort_of_total`), the window takes all records, and the records of a
compound are its rows. -/
theorem Query.PlainExcept.results {query : Query} {first later : Nat} {collations : List Collation}
    (shape : query.PlainExcept first later collations) (context : EvalContext) :
    query.results context [[]] = CompoundOperator.except.combine collations (context.subqueries first []).rows
      (context.subqueries later []).rows := by
  unfold Query.results
  dsimp only
  rw [stableSort_of_total _ (by simp [shape.orderBy, compareSort])]
  simp [Query.uniqueRecords, shape.compound, shape.orderBy, shape.limit, shape.offset, Query.compoundRecords,
    Compound.rows, Compound.combined, Function.comp_def]

/-- For every query of the shape {name}`Query.PlainExcept` and every context in which both terms end done, the
compound ends done. Proof sketch: the left term runs into a table and ends done, the right term ends done, and
no {lit}`UNION ALL` term follows. -/
theorem Query.PlainExcept.ending {query : Query} {first later : Nat} {collations : List Collation}
    (shape : query.PlainExcept first later collations) (context : EvalContext)
    (leftDone : (context.subqueries first []).ending = .done) (rightDone : (context.subqueries later []).ending = .done) :
    Compound.ending context query { first, rest := [(.except, later)], collations } [] = .done := by
  have bind : query.bindWindow context.parameters = some query :=
    Query.bindWindow_literal _ query shape.limitParameter shape.offsetParameter
  simp [Compound.ending, bind, shape.orderBy, shape.offset, shape.limit, chainEnd, stepEnd, fillSteps, directTerms,
    leftDone, rightDone, RunEnd.intoTable]

end Belay.Sqlite.Model.Resolved
