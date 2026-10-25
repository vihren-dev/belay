import Belay.Sqlite.Model.SimpleResultsLaws
import Belay.Sqlite.Model.SimpleSubqueryRun
import Belay.Sqlite.Model.TableSourceLaws
import Belay.Sqlite.Model.CompoundRun

set_option doc.verso true

/-! The run of the subqueries of {lit}`SELECT … FROM before.t WHERE p EXCEPT SELECT … FROM t` as a subquery of a
statement (ADR 0017, S6). The compound subquery has no source and two terms, which are the subqueries 1 and 2 of
the statement. Each term is a simple query of one table; the first reads the table of the initial database. The
module gives the source rows of the two kinds of term, the run of a simple subquery over the optional initial
database, and the rows and the fault of the compound: when the terms end without a failure and the rows of the
first term are identical where they compare equal, the rows are the first term without the rows that equal a row
of the second, and there is no fault. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every context, database, optional initial database, query whose only source is the table at a position as
an inner join without a condition, and database with that table, the source rows are the rows of the table in scan
order, with the width of the table and no fault, whatever the initial database is. Proof sketch: unfold the join of
the one source. -/
theorem Query.source_first_from (context : EvalContext) (query : Query) (database : Database) (initial : Option Database)
    (position : Nat) (table : Table) (sources : query.sources = [QuerySource.first position])
    (present : database.table position = some table) :
    query.source context database initial =
      some { rows := sourceRows table, width := table.shape.columns.length, fault := .none } := by
  simp [Query.source, sources, List.foldlM, QuerySource.join, QuerySource.first, QuerySource.joinTable, joinRows,
    joinRow, joinMatches, QuerySource.matches, bind, Option.bind, pure, present]

/-- For every context, database, initial database, query whose only source is the table at a position of the
initial database as an inner join without a condition, and initial database with that table, the source rows are
the rows of that table in scan order, with the width of the table and no fault, whatever the current database is.
Proof sketch: unfold the join of the one source. -/
theorem Query.source_initialTable (context : EvalContext) (query : Query) (database initial : Database)
    (position : Nat) (table : Table)
    (sources : query.sources = [{ kind := .inner, source := .initialTable position, condition := none }])
    (present : initial.table position = some table) :
    query.source context database (some initial) =
      some { rows := sourceRows table, width := table.shape.columns.length, fault := .none } := by
  simp [Query.source, sources, List.foldlM, QuerySource.join, QuerySource.joinTable, joinRows, joinRow,
    joinMatches, QuerySource.matches, bind, Option.bind, pure, present]

/-- For every context, database, optional initial database and query without sources, the source is the one row
with no cells and no fault. Proof sketch: the fold over no source returns its start. -/
theorem Query.source_noFrom_from (context : EvalContext) (query : Query) (database : Database)
    (initial : Option Database) (none_ : query.sources = []) :
    query.source context database initial = some { rows := [[]], width := 0, fault := .none } := by
  simp only [Query.source, none_, List.foldlM]
  rfl

/-- For every simple query that reads no cell of an outer query, with source rows in a context, database and
optional initial database, without fault, and with expressions that have no fallible call and no fault: the run as
a subquery has the one result as its rows, no fault and certain rows, and ends done. It is
{name}`Query.subqueryRun_simple` for a source that may read the initial database. Proof sketch: as
{name}`Query.subqueryRun_simple`; the source rows after the empty outer row are the source rows. -/
theorem Query.subqueryRun_simple_from (context : EvalContext) (database : Database) (initial : Option Database)
    (query : Query) (simple : query.Simple) (outer : query.outer = 0) (source : SourceRows)
    (found : query.source context database initial = some source)
    (clean : source.fault = .none) (plain : query.expressions.all (!·.any Expr.isFallibleCall) = true)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate context row).2 = .none) :
    query.subqueryRun context database [] initial =
      { rows := query.results context source.rows, fault := .none,
        firstCertain := query.windowCertain context source.rows (some 1), rowsCertain := true, ending := .done } := by
  have after : query.sourceAfter context [] database initial = some source := by
    simpa [Query.sourceAfter, outer, Query.source] using found
  unfold Query.subqueryRun
  rw [after]
  simp only [simple.bindWindow context.parameters, simple.run_of_faultless context plain source.rows faultless, clean]
  simp [Fault.join, Fault.soften, Query.windowCertain, certainCut, simple.limit, simple.offset]

/-- For every simple query as in {name}`Query.subqueryRun_simple_from`, the rows of the run as a subquery are the one
result, it has no fault, and it ends done. Proof sketch: read the three fields of {name}`Query.subqueryRun_simple_from`. -/
theorem Query.subqueryRun_simple_fields (context : EvalContext) (database : Database) (initial : Option Database)
    (query : Query) (simple : query.Simple) (outer : query.outer = 0) (source : SourceRows)
    (found : query.source context database initial = some source)
    (clean : source.fault = .none) (plain : query.expressions.all (!·.any Expr.isFallibleCall) = true)
    (faultless : ∀ row ∈ [] :: source.rows, ∀ expression ∈ query.expressions,
      (expression.evaluate context row).2 = .none) :
    (query.subqueryRun context database [] initial).rows = query.results context source.rows ∧
      (query.subqueryRun context database [] initial).fault = .none ∧
      (query.subqueryRun context database [] initial).ending = .done := by
  rw [Query.subqueryRun_simple_from context database initial query simple outer source found clean plain faultless]
  exact ⟨rfl, rfl, rfl⟩

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

/-- For every query of the shape {name}`Query.PlainExcept`, context, database and optional initial database in which
both terms end done and the rows of the first term are identical where they compare equal
({name}`equalRowsIdentical`): the run of the query as a subquery has as rows the first term without the rows that
equal a row of the second term, and it has no fault. In plain words: a compound that SQLite runs without failure and
whose kept rows do not depend on the plan has exactly the rows of the model. Proof sketch: {name}`Query.PlainExcept.results`
for the rows; the compound ends done ({name}`Query.PlainExcept.ending`), and the rows are certain because the first
term is identical, so the fault is none. -/
theorem Query.PlainExcept.subqueryRun {query : Query} {first later : Nat} {collations : List Collation}
    (shape : query.PlainExcept first later collations) (context : EvalContext) (database : Database)
    (initial : Option Database)
    (leftDone : (context.subqueries first []).ending = .done) (rightDone : (context.subqueries later []).ending = .done)
    (identical : equalRowsIdentical collations (context.subqueries first []).rows = true) :
    (query.subqueryRun context database [] initial).rows = CompoundOperator.except.combine collations
      (context.subqueries first []).rows (context.subqueries later []).rows ∧
    (query.subqueryRun context database [] initial).fault = .none := by
  have after : query.sourceAfter context [] database initial =
      some { rows := [[]], width := 0, fault := .none, outer := [] } := by
    simp [Query.sourceAfter, shape.sources, shape.outer]
  have bind : query.bindWindow context.parameters = some query :=
    Query.bindWindow_literal _ query shape.limitParameter shape.offsetParameter
  unfold Query.subqueryRun
  rw [after]
  simp only [bind]
  unfold Query.run Query.compoundRun
  simp only [shape.compound, bind, Option.map_some]
  have ended := shape.ending context leftDone rightDone
  simp only [List.headD_cons, ended]
  refine ⟨?_, ?_⟩
  · simpa using shape.results context
  · simp [Compound.combined, CompoundOperator.keepsCertain, identical, Fault.join, Fault.soften]

end Belay.Sqlite.Model.Resolved
