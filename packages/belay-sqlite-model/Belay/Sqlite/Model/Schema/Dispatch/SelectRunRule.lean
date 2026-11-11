import Belay.Sqlite.Model.Schema.Dispatch.SelectExecutionRule
import Belay.Sqlite.Model.Queries.Evaluation.SelectRunRule

set_option doc.verso true

/-! The run rule of a SELECT (ADR 0027, D5): the run of a query that is no compound, with its
window bound, splits into the obligations of its phases. It has no window mismatch; it overflows
exactly when an aggregate fails ({lit}`Query.fails`); and it has no fault exactly when no
expression certainly or possibly fails ({lit}`Query.mustFail`, {lit}`Query.mayFail`) and
{lit}`SELECT DISTINCT` keeps the same rows in every order ({lit}`Query.distinctCertain`). -/

namespace Belay.Sqlite.Model

/-- For every clock value, counters, values, database, subqueries and optional initial database,
the values of the parameters of the statement's context ({name}`Resolved.statementContext`) are
the given values. Proof sketch: every depth of {name}`Resolved.subqueryContext` keeps them. -/
@[simp] theorem Resolved.statementContext_parameters (clock : Int) (counters : Counters) (parameters : List Value)
    (database : Database) (subqueries : List Resolved.Query) (initial : Option Database) :
    (Resolved.statementContext clock counters parameters database subqueries initial).parameters = parameters := by
  unfold Resolved.statementContext
  generalize subqueries.length = depth
  cases depth <;> rfl

/-- For every connection, clock value, values, query that is no compound, subqueries, source
rows and query {lit}`bound` that the window binds to with the values: the query is ready
({name}`Connection.SelectReady`) when each counter that it reads is known, it has the source rows,
no nested subquery has a fallible call, the source does not possibly fail, and {lit}`bound` over
the source rows has no failing aggregate, does not certainly or possibly fail, and keeps the same
rows for {lit}`DISTINCT` in every order. Proof sketch: {name}`Resolved.Query.run_clean_iff` in
the context of the statement, whose values are the given ones
({name}`Resolved.statementContext_parameters`). -/
theorem Connection.SelectReady.of_phases {connection : Connection} {value : Int} {parameters : List Value}
    {query : Resolved.Query} {subqueries : List Resolved.Query} {source : Resolved.SourceRows} {bound : Resolved.Query}
    (single : query.compound = none)
    (known : connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (connection.queryContextAt value parameters query subqueries) connection.state.database =
      some source)
    (plain : Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true)
    (sourceCertain : source.fault ≠ .may)
    (window : query.bindWindow parameters = some bound)
    (noOverflow : bound.fails (connection.queryContextAt value parameters query subqueries) source.rows = false)
    (noMustFail : bound.mustFail (connection.queryContextAt value parameters query subqueries) source.rows = false)
    (noMayFail : bound.mayFail (connection.queryContextAt value parameters query subqueries) source.rows = false)
    (distinct : bound.distinctCertain (connection.queryContextAt value parameters query subqueries) source.rows = true) :
    connection.SelectReady value parameters query subqueries source bound := by
  have clean := (Resolved.Query.run_clean_iff (connection.queryContextAt value parameters query subqueries) query
    source.rows single (by simpa using window)).mpr ⟨noOverflow, noMustFail, noMayFail, distinct⟩
  exact ⟨known, found, plain, sourceCertain, window, clean.1, clean.2.1, clean.2.2⟩

end Belay.Sqlite.Model
