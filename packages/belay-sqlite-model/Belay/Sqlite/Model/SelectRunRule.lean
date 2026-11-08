import Belay.Sqlite.Model.SelectExecutionRule

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

namespace Resolved

/-- Run rule: for every context, query that is no compound, rows and query {lit}`bound` that the
window binds to with the values of the context ({name}`Query.bindWindow`), the run of the query
({name}`Query.run`) is: the result rows of {lit}`bound`; the fault {lean}`Fault.must` when
{lit}`bound` certainly fails ({name}`Query.mustFail`), else {lean}`Fault.may` when it possibly
fails ({name}`Query.mayFail`) or its {lit}`DISTINCT` is uncertain ({name}`Query.distinctCertain`),
else {lean}`Fault.none`; the overflow of {name}`Query.fails`; and no mismatch. Proof sketch: the
definition of {name}`Query.run`. -/
theorem Query.run_single (context : EvalContext) (query : Query) (rows : List (List Value)) {bound : Query}
    (single : query.compound = none) (window : query.bindWindow context.parameters = some bound) :
    query.run context rows =
      { rows := bound.results context rows,
        fault := if bound.mustFail context rows then .must
          else if bound.mayFail context rows || !bound.distinctCertain context rows then .may else .none,
        overflow := bound.fails context rows, mismatch := false } := by
  simp [Query.run, single, window]

/-- For every context, query that is no compound, rows and query {lit}`bound` that the window
binds to: the run has no mismatch, no overflow and no fault exactly when {lit}`bound` has no
failing aggregate ({name}`Query.fails`), does not certainly fail ({name}`Query.mustFail`), does
not possibly fail ({name}`Query.mayFail`), and keeps the same rows for {lit}`DISTINCT` in every
order ({name}`Query.distinctCertain`). Proof sketch: {name}`Query.run_single` and a case split
on the three Booleans of the fault. -/
theorem Query.run_clean_iff (context : EvalContext) (query : Query) (rows : List (List Value)) {bound : Query}
    (single : query.compound = none) (window : query.bindWindow context.parameters = some bound) :
    ((query.run context rows).mismatch = false ∧ (query.run context rows).overflow = false ∧
        (query.run context rows).fault = .none) ↔
      bound.fails context rows = false ∧ bound.mustFail context rows = false ∧
        bound.mayFail context rows = false ∧ bound.distinctCertain context rows = true := by
  rw [Query.run_single context query rows single window]
  cases bound.mustFail context rows <;> cases bound.mayFail context rows <;>
    cases bound.distinctCertain context rows <;> simp

end Resolved

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
