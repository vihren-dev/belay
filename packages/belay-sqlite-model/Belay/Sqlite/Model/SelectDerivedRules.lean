import Belay.Sqlite.Model.Subqueries

set_option doc.verso true

/-! The source rule of a derived {lit}`SELECT` (ADR 0027, A17): a query whose only source is a
derived table, a view or a common table expression reads the source as a subquery of the statement
({lit}`Source.subquery`). When the run of that subquery has no fault, ends done and has certain
complete rows, the source rows of the query are the rows of the run, so a proof about the inner
query serves the outer query. When the complete rows are not certain, the query has no source
rows, and the model does not describe the statement. -/

namespace Belay.Sqlite.Model.Resolved

/-- Derived source rule: for every context, database, optional initial database, query whose only
source is an inner join of subquery {lit}`index` of {lit}`width` columns without a condition, when
the run of the subquery for the empty outer row ({name}`EvalContext.subqueries`)

* has the fault {lean}`Fault.none`,
* ends with {lean}`RunEnd.done`, and
* has certain complete rows ({name}`SubqueryRun.sourceCertain`),

then the source rows of the query ({name}`Query.source`) are the rows of the run, with the width
field {lit}`width` and no fault. The rule does not prove that each row has {lit}`width` cells.
Proof sketch: the one join of the empty row with each row of the run
keeps the row, because a join without a condition matches every row. -/
theorem Query.source_derived (context : EvalContext) (database : Database) (initial : Option Database)
    (query : Query) (index width : Nat)
    (single : query.sources = [{ kind := .inner, source := .subquery index width, condition := none }])
    (clean : (context.subqueries index []).fault = .none) (ended : (context.subqueries index []).ending = .done)
    (certain : (context.subqueries index []).sourceCertain = true) :
    query.source context database initial =
      some { rows := (context.subqueries index []).rows, width, fault := .none } := by
  simp [Query.source, single, List.foldlM, QuerySource.join, clean, ended, certain, joinRows, joinRow,
    joinMatches, QuerySource.matches, bind, Option.bind, pure]

/-- Uncertain derived source rule: for every context, database, optional initial database, query
whose sources start with a join of subquery {lit}`index` of {lit}`width` columns, when the run of
the subquery for the empty outer row does not have certain complete rows
({name}`SubqueryRun.sourceCertain`), the query has no source rows ({name}`Query.source`). So no
proof about the outer query follows from a window of the inner query that can choose different
rows. -/
theorem Query.source_derived_uncertain (context : EvalContext) (database : Database) (initial : Option Database)
    (query : Query) (kind : JoinKind) (index width : Nat) (condition : Option Expr) (rest : List QuerySource)
    (sources : query.sources = { kind, source := .subquery index width, condition } :: rest)
    (uncertain : (context.subqueries index []).sourceCertain = false) :
    query.source context database initial = none := by
  simp [Query.source, sources, QuerySource.join, uncertain, bind, Option.bind]

/-- Unwindowed certainty rule: for every context, query without {lit}`OFFSET`, rows and choice of
complete rows, the window without {lit}`LIMIT` is certain ({name}`Query.windowCertain`): a window
that keeps every record has no cut. So a derived query without {lit}`LIMIT` and {lit}`OFFSET`
has certain complete rows in every order. -/
theorem Query.windowCertain_unwindowed (context : EvalContext) {query : Query} (noOffset : query.offset = 0)
    (rows : List (List Value)) (wholeRows : Bool) : query.windowCertain context rows none wholeRows = true := by
  simp [Query.windowCertain, noOffset, certainCut]

end Belay.Sqlite.Model.Resolved
