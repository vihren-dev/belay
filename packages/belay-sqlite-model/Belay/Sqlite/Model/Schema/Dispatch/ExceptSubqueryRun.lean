import Belay.Sqlite.Model.Schema.Dispatch.PlainQueryRules
import Belay.Sqlite.Model.Schema.Dispatch.TableSourceLaws
import Belay.Sqlite.Model.Queries.Evaluation.ExceptSubqueryRun

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

/-- For every query of the shape {name}`Query.PlainExcept`, context, database and optional initial database in which
both terms end done and the rows of the first term are identical where they compare equal
({name}`equalRowsIdentical`): the run of the query as a subquery has as rows the distinct rows of the first term that
equal no row of the second term ({name}`CompoundOperator.combine`), and it has no fault. In plain words: a compound that SQLite runs without failure and
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
